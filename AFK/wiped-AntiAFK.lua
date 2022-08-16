--[[
 		__      __.__                  .___                     .__  __   
		/  \    /  \__|_____   ____   __| _/          ________ __|__|/  |_ 
		\   \/\/   /  \____ \_/ __ \ / __ |  ______  / ____/  |  \  \   __\
 		\        /|  |  |_> >  ___// /_/ | /_____/ < <_|  |  |  /  ||  |  
 		 \__/\  / |__|   __/ \___  >____ |          \__   |____/|__||__|  
    		   \/     |__|        \/     \/             |__|               
     			\_Hey there! (V 0.1.0) </ 2022 created by quit
--]]

--</ Processing lua script.
local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 79) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local l = gBits32();
		local r = gBits32();
		return ((-2 * gBit(r, 32)) + 1) * (2 ^ (gBit(r, 21, 31) - 1023)) * ((((gBit(r, 1, 20) * (2 ^ 32)) + l) / (2 ^ 52)) + 1);
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		for Idx = 1, gBits32() do
			Lines[Idx] = gBits32();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local VIP = 1;
			local Top = -1;
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local function Loop()
				local Instr = Instr;
				local Const = Const;
				local Proto = Proto;
				local Params = Params;
				local _R = _R;
				local Vararg = {};
				local Lupvals = {};
				local Stk = {};
				for Idx = 0, PCount do
					if (Idx >= Params) then
						Vararg[Idx - Params] = Args[Idx + 1];
					else
						Stk[Idx] = Args[Idx + 1];
					end
				end
				local Varargsz = (PCount - Params) + 1;
				local Inst;
				local Enum;
				while true do
					Inst = Instr[VIP];
					Enum = Inst[1];
					if (Enum <= 6) then
						if (Enum <= 2) then
							if (Enum <= 0) then
								local A = Inst[2];
								Stk[A] = Stk[A]();
							elseif (Enum == 1) then
								Stk[Inst[2]] = Inst[3] ~= 0;
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum <= 4) then
							if (Enum == 3) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum == 5) then
							do
								return;
							end
						else
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 10) then
						if (Enum <= 8) then
							if (Enum == 7) then
								VIP = Inst[3];
							else
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum == 9) then
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]]();
						end
					elseif (Enum <= 12) then
						if (Enum == 11) then
							if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Env[Inst[3]];
						end
					elseif (Enum > 13) then
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					else
						local A = Inst[2];
						Stk[A](Stk[A + 1]);
					end
					VIP = VIP + 1;
				end
			end
			A, B = _R(PCall(Loop));
			if not A[1] then
				local line = Chunk[4][VIP] or "?";
				error("Script error at [" .. line .. "]:" .. A[2]);
			else
				return Unpack(A, 2, B);
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)();
end
VMCall("LOL!0D3O0003043O0077616974026O00D03F030A3O006C6F6164737472696E6703043O0067616D6503073O00482O747047657403303O00682O7470733A2O2F3O772E736372697074626C6F782E636F6D2F7261772F5365727665722D42726F777365725F383003173O00437265646974732062656C6F6E6720746F20717569742103073O0067657467656E7603073O006372656469747303073O00506C6179657273030B3O004C6F63616C506C6179657203043O004B69636B032B3O004C656176652074686520637265646974732C20736B69642E204D61796265206E6578742074696D65203A2800213O00120C3O00013O001208000100024O000D3O0002000100120C3O00033O00120C000100043O002004000100010005001208000300064O0001000400014O0006000100044O00025O00022O000A3O000100010012083O00073O00120C000100086O00010001000200200E0001000100090006090001001600013O0004073O0016000100120C000100086O00010001000200200E00010001000900060B0001002000013O0004073O0020000100120C000100043O00200E00010001000A00200E00010001000B00200400010001000C0012080003000D4O000300010003000100120C000100013O001208000200024O000D0001000200010004073O001F00012O00053O00017O00213O00013O00013O00013O00023O00023O00023O00023O00023O00023O00023O00023O00033O00043O00043O00043O00043O00043O00043O00043O00043O00043O00043O00053O00053O00053O00053O00053O00053O00063O00063O00063O00073O00093O00", GetFEnv());

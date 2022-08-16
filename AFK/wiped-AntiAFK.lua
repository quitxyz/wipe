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
								do
									return;
								end
							elseif (Enum == 1) then
								local NewProto = Proto[Inst[3]];
								local NewUvals;
								local Indexes = {};
								NewUvals = Setmetatable({}, {__index=function(_, Key)
									local Val = Indexes[Key];
									return Val[1][Val[2]];
								end,__newindex=function(_, Key, Value)
									local Val = Indexes[Key];
									Val[1][Val[2]] = Value;
								end});
								for Idx = 1, Inst[4] do
									VIP = VIP + 1;
									local Mvm = Instr[VIP];
									if (Mvm[1] == 3) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							else
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum <= 4) then
							if (Enum > 3) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							else
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum > 5) then
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 10) then
						if (Enum <= 8) then
							if (Enum == 7) then
								Stk[Inst[2]] = Inst[3];
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum == 9) then
							local A = Inst[2];
							Stk[A] = Stk[A]();
						elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 12) then
						if (Enum > 11) then
							Stk[Inst[2]] = Env[Inst[3]];
						else
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum > 13) then
						Stk[Inst[2]] = Upvalues[Inst[3]];
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
VMCall("LOL!103O0003173O00437265646974732062656C6F6E6720746F20717569742103073O0067657467656E7603073O006372656469747303043O0067616D6503073O00506C6179657273030B3O004C6F63616C506C6179657203043O004B69636B032B3O004C656176652074686520637265646974732C20736B69642E204D61796265206E6578742074696D65203A2803043O0077616974026O00E03F030A3O0047657453657276696365030B3O005669727475616C5573657203053O0049646C656403073O00636F2O6E65637403053O007072696E74035O002D3O0012073O00013O00120C000100024O0009000100010002002004000100010003002O060001000B00013O0004053O000B000100120C000100024O000900010001000200200400010001000300060A0001001500013O0004053O0015000100120C000100043O002004000100010005002004000100010006002002000100010007001207000300084O000B00010003000100120C000100093O0012070002000A4O000D0001000200010004053O0014000100120C000100093O0012070002000A4O000D00010002000100120C000100043O00200200010001000B0012070003000C4O000800010003000200120C000200043O00200200020002000B001207000400054O000800020004000200200400020002000600200400020002000D00200200020002000E00060100043O000100012O00033O00014O000B00020004000100120C000200093O0012070003000A4O000D00020002000100120C0002000F3O001207000300104O000D0002000200016O00013O00013O000A3O00030B3O0042752O746F6E32446F776E03073O00566563746F72322O033O006E6577028O0003093O00776F726B7370616365030D3O0043752O72656E7443616D65726103063O00434672616D6503043O0077616974026O00F03F03093O0042752O746F6E325570001D4O000E7O0020025O000100120C000200023O002004000200020003001207000300043O001207000400044O000800020004000200120C000300053O0020040003000300060020040003000300072O000B3O0003000100120C3O00083O001207000100094O000D3O000200012O000E7O0020025O000A00120C000200023O002004000200020003001207000300043O001207000400044O000800020004000200120C000300053O0020040003000300060020040003000300072O000B3O0003000100120C3O00083O001207000100094O000D3O000200016O00017O001D3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000C3O000C3O000C3O000D3O000D3O000D3O000D3O000D3O000D3O000D3O000D3O000D3O000D3O000D3O000E3O000E3O000E3O000F3O002D3O00013O00023O00023O00023O00023O00023O00023O00023O00023O00023O00023O00033O00033O00033O00033O00033O00033O00043O00043O00043O00053O00083O00083O00083O00093O00093O00093O00093O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000F3O000F3O000A3O00103O00103O00103O00113O00113O00113O00113O00", GetFEnv());

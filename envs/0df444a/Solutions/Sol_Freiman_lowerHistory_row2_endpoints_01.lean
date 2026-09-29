-- Prove2me | solution 1 for Freiman.lowerHistory_row2_endpoints_01
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-14T01:17:16.307427+00:00
-- url     : https://prove2.me/submissions/217a12db-bd83-44e9-a64e-62695831fd38

import Definitions.Def_Freiman_lowerHistoryVerification
import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace H5Row2Fast
private theorem inv_three (a b : ℚ) :
    lowerHistoryInv ⟨a,b,0,0⟩ =
      ⟨a / (a^2 - 3*b^2), -b / (a^2 - 3*b^2), 0, 0⟩ := by
  have hd : (a^2 + 3*b^2)^2 - 3*(2*a*b)^2 = (a^2-3*b^2)^2 := by ring
  simp only [lowerHistoryInv, certFieldScale, certFieldMul]
  dsimp
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, sub_zero, add_zero,
    neg_zero, zero_mul]
  rw [hd]
  by_cases h : a^2 - 3*b^2 = 0
  · simp [h]
  · congr 1 <;> field_simp <;> ring

private theorem inv_twenty_one (a d : ℚ) :
    lowerHistoryInv ⟨a,0,0,d⟩ =
      ⟨a / (a^2 - 21*d^2), 0, 0, -d / (a^2 - 21*d^2)⟩ := by
  simp only [lowerHistoryInv, certFieldScale, certFieldMul]
  dsimp
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, sub_zero, add_zero,
    neg_zero, zero_mul]
  by_cases h : a^2 - 21*d^2 = 0
  · simp [h]
  · congr 1 <;> field_simp <;> ring
end H5Row2Fast
set_option Elab.async false
set_option linter.all false
private theorem bsize0 : lowerHistoryBounds01.size = 200 := by rfl
private theorem bsize1 : lowerHistoryBounds02.size = 200 := by rfl
private theorem bsize2 : lowerHistoryBounds03.size = 200 := by rfl
private theorem bsize3 : lowerHistoryBounds04.size = 200 := by rfl
private theorem bsize4 : lowerHistoryBounds05.size = 200 := by rfl
private theorem bsize5 : lowerHistoryBounds06.size = 188 := by rfl
private def p0 : LowerHistoryPath := ⟨.right,6,[1],([2],[3]),false,[(([2],[]),true),(([1],[]),true)],([1,2,2],[3,1,3,1]),(false,false),false,2,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩
private def p1 : LowerHistoryPath := ⟨.right,21,[2],([2],[3]),false,[(([2],[]),true),(([1],[]),true)],([2,2,2],[3,1,3,1]),(false,false),false,2,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩
private def p2 : LowerHistoryPath := ⟨.right,36,[3],([2],[3]),false,[(([2],[]),true),(([1],[]),true)],([3,2,2],[3,1,3,1]),(false,false),false,2,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩
private def p3 : LowerHistoryPath := ⟨.right,66,[3,1,3],([2],[3]),false,[(([2],[]),true),(([1],[]),true)],([3,1,3,2,2],[3,1,3,1]),(false,false),false,2,⟨(5/19),(4/15),(3/4),(4/5)⟩,2⟩
private theorem canonical_endpoints : lowerHistoryEndpointComparisons p0 = [([836,1139,834,1149].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 884))),
([836,1139,834,271].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 880))),
([836,1139,283,436].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 884))),
([836,1139,283,841].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 885))),
([836,259,834,1149].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1179))),
([836,259,834,271].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1175))),
([836,259,283,436].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1179))),
([836,259,283,841].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1177))),
([284,429,834,1149].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 884))),
([284,429,834,271].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 880))),
([284,429,283,436].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 884))),
([284,429,283,841].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 885))),
([284,819,834,1149].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 895))),
([284,819,834,271].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 893))),
([284,819,283,436].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 895))),
([284,819,283,841].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 896)))] := by
  norm_num only [List.map_cons, List.map_nil, lowerHistoryBound, lowerHistoryBounds, Array.getElem?_append, Array.size_append, bsize0, bsize1, bsize2, bsize3, bsize4, bsize5]
  change lowerHistoryEndpointComparisons p0 = [([⟨false,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,true,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,false,⟨⟨(12011/16798),0,0,(973/50394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨false,true,⟨⟨(411421/870758),0,0,(2467/124394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(6941/16810),0,0,(-1/16810)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(-1075846/1002947),(2931611/3008841),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩)),
([⟨false,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,true,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,false,⟨⟨(12011/16798),0,0,(973/50394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨true,false,⟨⟨(411421/870758),0,0,(2467/124394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(6941/16810),0,0,(-1/16810)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(-6957009/6237506),(6234467/6237506),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩)),
([⟨false,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,true,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,false,⟨⟨(12011/16798),0,0,(973/50394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨true,true,⟨⟨(2879947/3109850),0,0,(120883/3109850)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(6941/16810),0,0,(-1/16810)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(-1075846/1002947),(2931611/3008841),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩)),
([⟨false,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,true,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,false,⟨⟨(12011/16798),0,0,(973/50394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨false,false,⟨⟨(2879947/3109850),0,0,(120883/3109850)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(6941/16810),0,0,(-1/16810)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(-1367629/1290421),(1248628/1290421),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(7298/17677),(-1/17677),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩)),
([⟨false,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,false,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,false,⟨⟨(12011/16798),0,0,(973/50394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨false,true,⟨⟨(411421/870758),0,0,(2467/124394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(6941/16810),0,0,(-1/16810)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(4160513/3159970),(-579309/1579985),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(89/214),(1/214),0,0⟩⟩⟩)),
([⟨false,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,false,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,false,⟨⟨(12011/16798),0,0,(973/50394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨true,false,⟨⟨(411421/870758),0,0,(2467/124394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(6941/16810),0,0,(-1/16810)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(1163038479/896895659),(-317947186/896895659),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(89/214),(1/214),0,0⟩⟩⟩)),
([⟨false,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,false,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,false,⟨⟨(12011/16798),0,0,(973/50394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨true,true,⟨⟨(2879947/3109850),0,0,(120883/3109850)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(6941/16810),0,0,(-1/16810)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(4160513/3159970),(-579309/1579985),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(89/214),(1/214),0,0⟩⟩⟩)),
([⟨false,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,false,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,false,⟨⟨(12011/16798),0,0,(973/50394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨false,false,⟨⟨(2879947/3109850),0,0,(120883/3109850)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(6941/16810),0,0,(-1/16810)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(2660286/2032855),(-1468807/4065710),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(7298/17677),(-1/17677),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(89/214),(1/214),0,0⟩⟩⟩)),
([⟨true,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,true,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,false,⟨⟨(12011/16798),0,0,(973/50394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨false,true,⟨⟨(411421/870758),0,0,(2467/124394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(6941/16810),0,0,(-1/16810)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(-1075846/1002947),(2931611/3008841),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩)),
([⟨true,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,true,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,false,⟨⟨(12011/16798),0,0,(973/50394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨true,false,⟨⟨(411421/870758),0,0,(2467/124394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(6941/16810),0,0,(-1/16810)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(-6957009/6237506),(6234467/6237506),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩)),
([⟨true,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,true,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,false,⟨⟨(12011/16798),0,0,(973/50394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨true,true,⟨⟨(2879947/3109850),0,0,(120883/3109850)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(6941/16810),0,0,(-1/16810)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(-1075846/1002947),(2931611/3008841),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩)),
([⟨true,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,true,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,false,⟨⟨(12011/16798),0,0,(973/50394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨false,false,⟨⟨(2879947/3109850),0,0,(120883/3109850)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(6941/16810),0,0,(-1/16810)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(-1367629/1290421),(1248628/1290421),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(7298/17677),(-1/17677),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩)),
([⟨true,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,false,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,false,⟨⟨(12011/16798),0,0,(973/50394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨false,true,⟨⟨(411421/870758),0,0,(2467/124394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(6941/16810),0,0,(-1/16810)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(-12467855/39114933),(7387071/13038311),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩)),
([⟨true,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,false,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,false,⟨⟨(12011/16798),0,0,(973/50394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨true,false,⟨⟨(411421/870758),0,0,(2467/124394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(6941/16810),0,0,(-1/16810)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(-13726399/40543789),(23458324/40543789),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩)),
([⟨true,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,false,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,false,⟨⟨(12011/16798),0,0,(973/50394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨true,true,⟨⟨(2879947/3109850),0,0,(120883/3109850)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(6941/16810),0,0,(-1/16810)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(-12467855/39114933),(7387071/13038311),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩)),
([⟨true,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,false,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,false,⟨⟨(12011/16798),0,0,(973/50394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨false,false,⟨⟨(2879947/3109850),0,0,(120883/3109850)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(6941/16810),0,0,(-1/16810)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(-1399514/4575129),(28175102/50326419),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(7298/17677),(-1/17677),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩))]
  norm_num (maxSteps := 1000000) [p0,lowerHistoryStateAt,lowerHistoryWordsAt,lowerHistoryReplay,lowerHistoryRawStep,lowerHistoryInitialState,lowerHistoryAdvance,lowerHistorySourceChoices,lowerHistoryNormalization,lowerHistoryFinalCuts,lowerHistoryH2,lowerHistoryH5,lowerHistoryH6,lowerHistoryH7,lowerHistoryH7Mixed,lowerHistoryH9,lowerHistoryH21,lowerHistoryH23,lowerHistoryHN,lowerHistoryZero,lowerHistoryConstantBound,lowerHistoryPB,lowerHistoryTheta,lowerHistoryTau,lowerHistoryComplement,lowerHistoryPull,lowerHistoryWH,lowerHistoryCF,lowerHistoryMatrix,lowerHistoryDiv,lowerHistoryAlpha,lowerHistoryBeta,lowerHistoryThreshold,lowerHistorySort,lowerHistoryLex,lowerHistoryAbs,lowerHistorySign,lowerHistoryQuadSign,lowerHistoryRatSign,lowerHistoryNeg,lowerHistoryRat,certFieldAdd,certFieldSub,certFieldMul,certFieldScale,H5Row2Fast.inv_three,H5Row2Fast.inv_twenty_one,lowerHistoryPick,← List.isSuffixOf_iff_suffix,List.isSuffixOf,List.isPrefixOf,beq_iff_eq,lowerHistoryEndpointComparisons,lowerHistoryFinalWords,lowerHistoryComparisons,lowerHistoryEndpointCases,lowerHistoryEqualCases,lowerHistoryNatural,lowerHistoryWordParity,lowerHistoryEndVal,lowerHistoryNormalCases,lowerHistoryScaleThreshold,lowerHistorySet,lowerHistoryGreater]
private theorem context1 : lowerHistoryEndpointComparisons p1 = lowerHistoryEndpointComparisons p0 := by rfl
private theorem context2 : lowerHistoryEndpointComparisons p2 = lowerHistoryEndpointComparisons p0 := by rfl
private theorem context3 : lowerHistoryEndpointComparisons p3 = lowerHistoryEndpointComparisons p0 := by rfl
theorem solution : ∀ p : LowerHistoryPath, p ∈ [lowerHistoryPathsR[5],lowerHistoryPathsR[20],lowerHistoryPathsR[35],lowerHistoryPathsR[65]] → lowerHistoryEndpointComparisons p = [([836,1139,834,1149].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 884))),
([836,1139,834,271].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 880))),
([836,1139,283,436].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 884))),
([836,1139,283,841].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 885))),
([836,259,834,1149].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1179))),
([836,259,834,271].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1175))),
([836,259,283,436].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1179))),
([836,259,283,841].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1177))),
([284,429,834,1149].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 884))),
([284,429,834,271].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 880))),
([284,429,283,436].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 884))),
([284,429,283,841].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 885))),
([284,819,834,1149].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 895))),
([284,819,834,271].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 893))),
([284,819,283,436].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 895))),
([284,819,283,841].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 896)))] := by
  intro p hp
  change p ∈ [p0,p1,p2,p3] at hp
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact canonical_endpoints
  · exact context1 |>.trans canonical_endpoints
  · exact context2 |>.trans canonical_endpoints
  · exact context3 |>.trans canonical_endpoints
#print axioms solution

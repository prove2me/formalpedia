-- Prove2me | solution 1 for Freiman.lowerHistory_row2_endpoints_02
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-14T01:17:25.124557+00:00
-- url     : https://prove2.me/submissions/157bf78a-f14c-4056-a3cb-97d46843ac8c

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
private def p0 : LowerHistoryPath := ⟨.right,8,[1],([2],[3]),false,[(([1],[]),true),(([1],[]),true)],([1,2,1],[3,1,3,1]),(false,false),false,2,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private def p1 : LowerHistoryPath := ⟨.right,23,[2],([2],[3]),false,[(([1],[]),true),(([1],[]),true)],([2,2,1],[3,1,3,1]),(false,false),false,2,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩
private def p2 : LowerHistoryPath := ⟨.right,38,[3],([2],[3]),false,[(([1],[]),true),(([1],[]),true)],([3,2,1],[3,1,3,1]),(false,false),false,2,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩
private def p3 : LowerHistoryPath := ⟨.right,68,[3,1,3],([2],[3]),false,[(([1],[]),true),(([1],[]),true)],([3,1,3,2,1],[3,1,3,1]),(false,false),false,2,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩
private theorem canonical_endpoints : lowerHistoryEndpointComparisons p0 = [([836,1139,858,1174].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 889))),
([836,1139,858,291].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 887))),
([836,1139,294,441].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 889))),
([836,1139,294,865].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 890))),
([836,259,858,1174].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1169))),
([836,259,858,291].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1167))),
([836,259,294,441].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1169))),
([836,259,294,865].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1166))),
([284,429,858,1174].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 889))),
([284,429,858,291].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 887))),
([284,429,294,441].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 889))),
([284,429,294,865].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 890))),
([284,819,858,1174].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 901))),
([284,819,858,291].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 900))),
([284,819,294,441].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 901))),
([284,819,294,865].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 902)))] := by
  norm_num only [List.map_cons, List.map_nil, lowerHistoryBound, lowerHistoryBounds, Array.getElem?_append, Array.size_append, bsize0, bsize1, bsize2, bsize3, bsize4, bsize5]
  change lowerHistoryEndpointComparisons p0 = [([⟨false,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,true,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,false,⟨⟨(669/370),0,0,(109/7770)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨false,true,⟨⟨(63393/49966),0,0,(4831/349762)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(-424339/431211),(110156/143737),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩)),
([⟨false,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,true,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,false,⟨⟨(669/370),0,0,(109/7770)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨true,false,⟨⟨(63393/49966),0,0,(4831/349762)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(-911737/893926),(703861/893926),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩)),
([⟨false,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,true,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,false,⟨⟨(669/370),0,0,(109/7770)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨true,true,⟨⟨(443751/178450),0,0,(4831/178450)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(-424339/431211),(110156/143737),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩)),
([⟨false,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,true,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,false,⟨⟨(669/370),0,0,(109/7770)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨false,false,⟨⟨(443751/178450),0,0,(4831/178450)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(-5747540/6023303),(4522279/6023303),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩)),
([⟨false,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,false,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,false,⟨⟨(669/370),0,0,(109/7770)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨false,true,⟨⟨(63393/49966),0,0,(4831/349762)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(228122/226435),(-491737/1358610),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(89/214),(1/214),0,0⟩⟩⟩)),
([⟨false,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,false,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,false,⟨⟨(669/370),0,0,(109/7770)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨true,false,⟨⟨(63393/49966),0,0,(4831/349762)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(127333832/128538289),(-45226773/128538289),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(89/214),(1/214),0,0⟩⟩⟩)),
([⟨false,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,false,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,false,⟨⟨(669/370),0,0,(109/7770)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨true,true,⟨⟨(443751/178450),0,0,(4831/178450)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(228122/226435),(-491737/1358610),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(89/214),(1/214),0,0⟩⟩⟩)),
([⟨false,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,false,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,false,⟨⟨(669/370),0,0,(109/7770)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨false,false,⟨⟨(443751/178450),0,0,(4831/178450)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(18767871/18977530),(-663122/1897753),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(89/214),(1/214),0,0⟩⟩⟩)),
([⟨true,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,true,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,false,⟨⟨(669/370),0,0,(109/7770)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨false,true,⟨⟨(63393/49966),0,0,(4831/349762)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(-424339/431211),(110156/143737),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩)),
([⟨true,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,true,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,false,⟨⟨(669/370),0,0,(109/7770)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨true,false,⟨⟨(63393/49966),0,0,(4831/349762)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(-911737/893926),(703861/893926),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩)),
([⟨true,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,true,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,false,⟨⟨(669/370),0,0,(109/7770)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨true,true,⟨⟨(443751/178450),0,0,(4831/178450)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(-424339/431211),(110156/143737),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩)),
([⟨true,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,true,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,false,⟨⟨(669/370),0,0,(109/7770)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨false,false,⟨⟨(443751/178450),0,0,(4831/178450)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(-5747540/6023303),(4522279/6023303),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩)),
([⟨true,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,false,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,false,⟨⟨(669/370),0,0,(109/7770)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨false,true,⟨⟨(63393/49966),0,0,(4831/349762)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(-1290038/5605743),(2010254/5605743),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩)),
([⟨true,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,false,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,false,⟨⟨(669/370),0,0,(109/7770)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨true,false,⟨⟨(63393/49966),0,0,(4831/349762)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(-1412716/5810519),(2129330/5810519),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩)),
([⟨true,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,false,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,false,⟨⟨(669/370),0,0,(109/7770)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨true,true,⟨⟨(443751/178450),0,0,(4831/178450)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(-1290038/5605743),(2010254/5605743),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩)),
([⟨true,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨false,false,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩,⟨true,false,⟨⟨(669/370),0,0,(109/7770)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨false,false,⟨⟨(443751/178450),0,0,(4831/178450)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(-3619073/18069909),(6198547/18069909),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩))]
  norm_num (maxSteps := 1000000) [p0,lowerHistoryStateAt,lowerHistoryWordsAt,lowerHistoryReplay,lowerHistoryRawStep,lowerHistoryInitialState,lowerHistoryAdvance,lowerHistorySourceChoices,lowerHistoryNormalization,lowerHistoryFinalCuts,lowerHistoryH2,lowerHistoryH5,lowerHistoryH6,lowerHistoryH7,lowerHistoryH7Mixed,lowerHistoryH9,lowerHistoryH21,lowerHistoryH23,lowerHistoryHN,lowerHistoryZero,lowerHistoryConstantBound,lowerHistoryPB,lowerHistoryTheta,lowerHistoryTau,lowerHistoryComplement,lowerHistoryPull,lowerHistoryWH,lowerHistoryCF,lowerHistoryMatrix,lowerHistoryDiv,lowerHistoryAlpha,lowerHistoryBeta,lowerHistoryThreshold,lowerHistorySort,lowerHistoryLex,lowerHistoryAbs,lowerHistorySign,lowerHistoryQuadSign,lowerHistoryRatSign,lowerHistoryNeg,lowerHistoryRat,certFieldAdd,certFieldSub,certFieldMul,certFieldScale,H5Row2Fast.inv_three,H5Row2Fast.inv_twenty_one,lowerHistoryPick,← List.isSuffixOf_iff_suffix,List.isSuffixOf,List.isPrefixOf,beq_iff_eq,lowerHistoryEndpointComparisons,lowerHistoryFinalWords,lowerHistoryComparisons,lowerHistoryEndpointCases,lowerHistoryEqualCases,lowerHistoryNatural,lowerHistoryWordParity,lowerHistoryEndVal,lowerHistoryNormalCases,lowerHistoryScaleThreshold,lowerHistorySet,lowerHistoryGreater]
private theorem context1 : lowerHistoryEndpointComparisons p1 = lowerHistoryEndpointComparisons p0 := by rfl
private theorem context2 : lowerHistoryEndpointComparisons p2 = lowerHistoryEndpointComparisons p0 := by rfl
private theorem context3 : lowerHistoryEndpointComparisons p3 = lowerHistoryEndpointComparisons p0 := by rfl
theorem solution : ∀ p : LowerHistoryPath, p ∈ [lowerHistoryPathsR[7],lowerHistoryPathsR[22],lowerHistoryPathsR[37],lowerHistoryPathsR[67]] → lowerHistoryEndpointComparisons p = [([836,1139,858,1174].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 889))),
([836,1139,858,291].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 887))),
([836,1139,294,441].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 889))),
([836,1139,294,865].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 890))),
([836,259,858,1174].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1169))),
([836,259,858,291].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1167))),
([836,259,294,441].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1169))),
([836,259,294,865].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1166))),
([284,429,858,1174].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 889))),
([284,429,858,291].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 887))),
([284,429,294,441].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 889))),
([284,429,294,865].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 890))),
([284,819,858,1174].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 901))),
([284,819,858,291].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 900))),
([284,819,294,441].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 901))),
([284,819,294,865].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 902)))] := by
  intro p hp
  change p ∈ [p0,p1,p2,p3] at hp
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact canonical_endpoints
  · exact context1 |>.trans canonical_endpoints
  · exact context2 |>.trans canonical_endpoints
  · exact context3 |>.trans canonical_endpoints
#print axioms solution

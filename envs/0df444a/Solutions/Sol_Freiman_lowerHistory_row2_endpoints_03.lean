-- Prove2me | solution 1 for Freiman.lowerHistory_row2_endpoints_03
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-14T01:17:34.17101+00:00
-- url     : https://prove2.me/submissions/cfe8274d-5244-46fa-bd2c-a96606ac12f1

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
private def p0 : LowerHistoryPath := ⟨.right,51,[3,1],([2],[3]),false,[(([2],[]),true),(([1],[]),true)],([3,1,2,2],[3,1,3,1]),(false,false),false,2,⟨(3/4),(4/5),(3/4),(4/5)⟩,2⟩
private def p1 : LowerHistoryPath := ⟨.right,81,[3,1,3,1],([2],[3]),false,[(([2],[]),true),(([1],[]),true)],([3,1,3,1,2,2],[3,1,3,1]),(false,false),false,2,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩
private theorem canonical_endpoints : lowerHistoryEndpointComparisons p0 = [([834,1149].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1119))),
([834,271].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1121))),
([283,436].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1119))),
([283,841].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1116)))] := by
  norm_num only [List.map_cons, List.map_nil, lowerHistoryBound, lowerHistoryBounds, Array.getElem?_append, Array.size_append, bsize0, bsize1, bsize2, bsize3, bsize4, bsize5]
  change lowerHistoryEndpointComparisons p0 = [([⟨false,false,⟨⟨(12011/16798),0,0,(973/50394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨false,true,⟨⟨(411421/870758),0,0,(2467/124394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(6941/16810),0,0,(-1/16810)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(149138/765637),(176166/765637),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(15/37),(-1/37),0,0⟩⟩⟩)),
([⟨false,false,⟨⟨(12011/16798),0,0,(973/50394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨true,false,⟨⟨(411421/870758),0,0,(2467/124394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(6941/16810),0,0,(-1/16810)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(532485/2699089),(619868/2699089),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(15/37),(-1/37),0,0⟩⟩⟩)),
([⟨true,false,⟨⟨(12011/16798),0,0,(973/50394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨true,true,⟨⟨(2879947/3109850),0,0,(120883/3109850)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(6941/16810),0,0,(-1/16810)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(149138/765637),(176166/765637),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(15/37),(-1/37),0,0⟩⟩⟩)),
([⟨true,false,⟨⟨(12011/16798),0,0,(973/50394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩,⟨false,false,⟨⟨(2879947/3109850),0,0,(120883/3109850)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(6941/16810),0,0,(-1/16810)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩], LowerHistoryComparison.bound (lowerHistoryComplement ⟨false,true,⟨⟨(2052469/10836001),(2541387/10836001),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(7298/17677),(-1/17677),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(15/37),(-1/37),0,0⟩⟩⟩))]
  norm_num (maxSteps := 1000000) [p0,lowerHistoryStateAt,lowerHistoryWordsAt,lowerHistoryReplay,lowerHistoryRawStep,lowerHistoryInitialState,lowerHistoryAdvance,lowerHistorySourceChoices,lowerHistoryNormalization,lowerHistoryFinalCuts,lowerHistoryH2,lowerHistoryH5,lowerHistoryH6,lowerHistoryH7,lowerHistoryH7Mixed,lowerHistoryH9,lowerHistoryH21,lowerHistoryH23,lowerHistoryHN,lowerHistoryZero,lowerHistoryConstantBound,lowerHistoryPB,lowerHistoryTheta,lowerHistoryTau,lowerHistoryComplement,lowerHistoryPull,lowerHistoryWH,lowerHistoryCF,lowerHistoryMatrix,lowerHistoryDiv,lowerHistoryAlpha,lowerHistoryBeta,lowerHistoryThreshold,lowerHistorySort,lowerHistoryLex,lowerHistoryAbs,lowerHistorySign,lowerHistoryQuadSign,lowerHistoryRatSign,lowerHistoryNeg,lowerHistoryRat,certFieldAdd,certFieldSub,certFieldMul,certFieldScale,H5Row2Fast.inv_three,H5Row2Fast.inv_twenty_one,lowerHistoryPick,← List.isSuffixOf_iff_suffix,List.isSuffixOf,List.isPrefixOf,beq_iff_eq,lowerHistoryEndpointComparisons,lowerHistoryFinalWords,lowerHistoryComparisons,lowerHistoryEndpointCases,lowerHistoryEqualCases,lowerHistoryNatural,lowerHistoryWordParity,lowerHistoryEndVal,lowerHistoryNormalCases,lowerHistoryScaleThreshold,lowerHistorySet,lowerHistoryGreater]
private theorem context1 : lowerHistoryEndpointComparisons p1 = lowerHistoryEndpointComparisons p0 := by rfl
theorem solution : ∀ p : LowerHistoryPath, p ∈ [lowerHistoryPathsR[50],lowerHistoryPathsR[80]] → lowerHistoryEndpointComparisons p = [([834,1149].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1119))),
([834,271].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1121))),
([283,436].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1119))),
([283,841].map lowerHistoryBound, LowerHistoryComparison.bound (lowerHistoryComplement (lowerHistoryBound 1116)))] := by
  intro p hp
  change p ∈ [p0,p1] at hp
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
  rcases hp with rfl | rfl
  · exact canonical_endpoints
  · exact context1 |>.trans canonical_endpoints
#print axioms solution

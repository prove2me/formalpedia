-- Prove2me | solution 1 for D1Bound5.firstPairGeometryRows_have_fixed_row
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:52:05.041573+00:00
-- url     : https://prove2.me/submissions/af71a273-e9a8-4ce5-bd53-086c4b6fe05c

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_FirstPairGeometryData_Definitions_001
import Definitions.Def_D1Bound5_FirstPairGeometryData_Definitions_002
import Definitions.Def_D1Bound5_FirstPairGeometryFixedRows_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Theorems.Thm_D1Bound5_firstPairGeometryRow_0_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_10_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_11_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_12_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_13_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_14_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_15_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_16_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_17_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_18_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_19_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_1_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_20_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_21_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_22_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_23_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_24_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_25_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_26_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_27_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_28_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_29_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_2_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_30_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_31_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_32_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_33_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_34_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_35_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_36_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_37_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_38_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_39_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_3_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_40_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_4_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_5_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_6_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_7_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_8_has_fixed_row
import Theorems.Thm_D1Bound5_firstPairGeometryRow_9_has_fixed_row

section
namespace D1Bound5





set_option maxRecDepth 100000
set_option maxHeartbeats 0



















































































theorem _root_.solution (g : FirstPairGeometryRow)
    (hg : g ∈ firstPairGeometryRows) :
    ∃ r ∈ oneSmallCutoffRows, FirstPairGeometryMatches g r := by
  simp only [firstPairGeometryRows,List.mem_cons,List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact firstPairGeometryRow_0_has_fixed_row
  · exact firstPairGeometryRow_1_has_fixed_row
  · exact firstPairGeometryRow_2_has_fixed_row
  · exact firstPairGeometryRow_3_has_fixed_row
  · exact firstPairGeometryRow_4_has_fixed_row
  · exact firstPairGeometryRow_5_has_fixed_row
  · exact firstPairGeometryRow_6_has_fixed_row
  · exact firstPairGeometryRow_7_has_fixed_row
  · exact firstPairGeometryRow_8_has_fixed_row
  · exact firstPairGeometryRow_9_has_fixed_row
  · exact firstPairGeometryRow_10_has_fixed_row
  · exact firstPairGeometryRow_11_has_fixed_row
  · exact firstPairGeometryRow_12_has_fixed_row
  · exact firstPairGeometryRow_13_has_fixed_row
  · exact firstPairGeometryRow_14_has_fixed_row
  · exact firstPairGeometryRow_15_has_fixed_row
  · exact firstPairGeometryRow_16_has_fixed_row
  · exact firstPairGeometryRow_17_has_fixed_row
  · exact firstPairGeometryRow_18_has_fixed_row
  · exact firstPairGeometryRow_19_has_fixed_row
  · exact firstPairGeometryRow_20_has_fixed_row
  · exact firstPairGeometryRow_21_has_fixed_row
  · exact firstPairGeometryRow_22_has_fixed_row
  · exact firstPairGeometryRow_23_has_fixed_row
  · exact firstPairGeometryRow_24_has_fixed_row
  · exact firstPairGeometryRow_25_has_fixed_row
  · exact firstPairGeometryRow_26_has_fixed_row
  · exact firstPairGeometryRow_27_has_fixed_row
  · exact firstPairGeometryRow_28_has_fixed_row
  · exact firstPairGeometryRow_29_has_fixed_row
  · exact firstPairGeometryRow_30_has_fixed_row
  · exact firstPairGeometryRow_31_has_fixed_row
  · exact firstPairGeometryRow_32_has_fixed_row
  · exact firstPairGeometryRow_33_has_fixed_row
  · exact firstPairGeometryRow_34_has_fixed_row
  · exact firstPairGeometryRow_35_has_fixed_row
  · exact firstPairGeometryRow_36_has_fixed_row
  · exact firstPairGeometryRow_37_has_fixed_row
  · exact firstPairGeometryRow_38_has_fixed_row
  · exact firstPairGeometryRow_39_has_fixed_row
  · exact firstPairGeometryRow_40_has_fixed_row

end D1Bound5
end

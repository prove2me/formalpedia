-- Prove2me | solution 1 for D1Bound5.oneSmallCutoffRows_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:48:06.369742+00:00
-- url     : https://prove2.me/submissions/9b7d69d5-3a55-4d6f-809e-d760a1a13e3c

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
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_0_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_10_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_11_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_12_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_13_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_14_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_15_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_16_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_17_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_18_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_19_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_1_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_20_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_21_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_22_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_23_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_24_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_25_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_26_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_27_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_28_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_29_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_2_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_30_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_31_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_32_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_33_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_34_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_35_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_36_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_37_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_38_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_39_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_3_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_40_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_41_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_42_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_43_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_44_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_45_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_46_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_47_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_48_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_49_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_4_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_50_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_51_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_52_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_53_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_54_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_55_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_56_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_5_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_6_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_7_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_8_valid
import Theorems.Thm_D1Bound5_oneSmallCutoffRow_9_valid

section
namespace D1Bound5
open QuadInt



namespace OneSmallCutoffRow



























end OneSmallCutoffRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0







































































































































































































































/-- Every arithmetic row is kernel checked separately. -/
theorem _root_.solution (r : OneSmallCutoffRow)
    (hr : r ∈ oneSmallCutoffRows) : r.Valid := by
  simp only [oneSmallCutoffRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact oneSmallCutoffRow_0_valid
  · exact oneSmallCutoffRow_1_valid
  · exact oneSmallCutoffRow_2_valid
  · exact oneSmallCutoffRow_3_valid
  · exact oneSmallCutoffRow_4_valid
  · exact oneSmallCutoffRow_5_valid
  · exact oneSmallCutoffRow_6_valid
  · exact oneSmallCutoffRow_7_valid
  · exact oneSmallCutoffRow_8_valid
  · exact oneSmallCutoffRow_9_valid
  · exact oneSmallCutoffRow_10_valid
  · exact oneSmallCutoffRow_11_valid
  · exact oneSmallCutoffRow_12_valid
  · exact oneSmallCutoffRow_13_valid
  · exact oneSmallCutoffRow_14_valid
  · exact oneSmallCutoffRow_15_valid
  · exact oneSmallCutoffRow_16_valid
  · exact oneSmallCutoffRow_17_valid
  · exact oneSmallCutoffRow_18_valid
  · exact oneSmallCutoffRow_19_valid
  · exact oneSmallCutoffRow_20_valid
  · exact oneSmallCutoffRow_21_valid
  · exact oneSmallCutoffRow_22_valid
  · exact oneSmallCutoffRow_23_valid
  · exact oneSmallCutoffRow_24_valid
  · exact oneSmallCutoffRow_25_valid
  · exact oneSmallCutoffRow_26_valid
  · exact oneSmallCutoffRow_27_valid
  · exact oneSmallCutoffRow_28_valid
  · exact oneSmallCutoffRow_29_valid
  · exact oneSmallCutoffRow_30_valid
  · exact oneSmallCutoffRow_31_valid
  · exact oneSmallCutoffRow_32_valid
  · exact oneSmallCutoffRow_33_valid
  · exact oneSmallCutoffRow_34_valid
  · exact oneSmallCutoffRow_35_valid
  · exact oneSmallCutoffRow_36_valid
  · exact oneSmallCutoffRow_37_valid
  · exact oneSmallCutoffRow_38_valid
  · exact oneSmallCutoffRow_39_valid
  · exact oneSmallCutoffRow_40_valid
  · exact oneSmallCutoffRow_41_valid
  · exact oneSmallCutoffRow_42_valid
  · exact oneSmallCutoffRow_43_valid
  · exact oneSmallCutoffRow_44_valid
  · exact oneSmallCutoffRow_45_valid
  · exact oneSmallCutoffRow_46_valid
  · exact oneSmallCutoffRow_47_valid
  · exact oneSmallCutoffRow_48_valid
  · exact oneSmallCutoffRow_49_valid
  · exact oneSmallCutoffRow_50_valid
  · exact oneSmallCutoffRow_51_valid
  · exact oneSmallCutoffRow_52_valid
  · exact oneSmallCutoffRow_53_valid
  · exact oneSmallCutoffRow_54_valid
  · exact oneSmallCutoffRow_55_valid
  · exact oneSmallCutoffRow_56_valid





end D1Bound5
end

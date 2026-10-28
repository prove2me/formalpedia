-- Prove2me | solution 1 for D1Bound5.oneSmallCutoffRows_finiteN2FixedBound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:24:25.502228+00:00
-- url     : https://prove2.me/submissions/2c145205-609d-49be-bf16-b7f4ec07f645

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallN2FixedArithmetic_Definitions
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_0_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_10_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_11_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_12_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_13_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_14_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_15_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_16_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_17_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_18_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_19_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_1_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_20_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_21_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_22_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_23_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_24_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_25_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_26_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_27_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_28_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_29_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_2_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_30_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_31_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_32_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_33_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_34_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_35_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_36_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_37_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_38_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_39_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_3_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_40_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_41_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_42_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_43_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_44_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_45_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_46_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_47_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_48_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_49_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_4_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_50_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_51_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_52_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_53_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_54_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_55_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_56_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_5_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_6_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_7_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_8_valid
import Theorems.Thm_D1Bound5_finiteN2CutoffWeights_9_valid

section
namespace D1Bound5
open QuadInt







set_option maxRecDepth 100000
set_option maxHeartbeats 0





































































































































































































































/-- Each of the57 actual cutoff triples has exact coefficient-square
certificates for the manuscript's M2, computed from the proved N2
integer coefficient vectors. -/
theorem _root_.solution (r : OneSmallCutoffRow)
    (hr : r ∈ oneSmallCutoffRows) :
    ∃ w : Fin 3 → Fin 2 → Fin 3 → ℚ, FiniteN2FixedBound r w := by
  simp only [oneSmallCutoffRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨finiteN2CutoffWeights_0,finiteN2CutoffWeights_0_valid⟩
  · exact ⟨finiteN2CutoffWeights_1,finiteN2CutoffWeights_1_valid⟩
  · exact ⟨finiteN2CutoffWeights_2,finiteN2CutoffWeights_2_valid⟩
  · exact ⟨finiteN2CutoffWeights_3,finiteN2CutoffWeights_3_valid⟩
  · exact ⟨finiteN2CutoffWeights_4,finiteN2CutoffWeights_4_valid⟩
  · exact ⟨finiteN2CutoffWeights_5,finiteN2CutoffWeights_5_valid⟩
  · exact ⟨finiteN2CutoffWeights_6,finiteN2CutoffWeights_6_valid⟩
  · exact ⟨finiteN2CutoffWeights_7,finiteN2CutoffWeights_7_valid⟩
  · exact ⟨finiteN2CutoffWeights_8,finiteN2CutoffWeights_8_valid⟩
  · exact ⟨finiteN2CutoffWeights_9,finiteN2CutoffWeights_9_valid⟩
  · exact ⟨finiteN2CutoffWeights_10,finiteN2CutoffWeights_10_valid⟩
  · exact ⟨finiteN2CutoffWeights_11,finiteN2CutoffWeights_11_valid⟩
  · exact ⟨finiteN2CutoffWeights_12,finiteN2CutoffWeights_12_valid⟩
  · exact ⟨finiteN2CutoffWeights_13,finiteN2CutoffWeights_13_valid⟩
  · exact ⟨finiteN2CutoffWeights_14,finiteN2CutoffWeights_14_valid⟩
  · exact ⟨finiteN2CutoffWeights_15,finiteN2CutoffWeights_15_valid⟩
  · exact ⟨finiteN2CutoffWeights_16,finiteN2CutoffWeights_16_valid⟩
  · exact ⟨finiteN2CutoffWeights_17,finiteN2CutoffWeights_17_valid⟩
  · exact ⟨finiteN2CutoffWeights_18,finiteN2CutoffWeights_18_valid⟩
  · exact ⟨finiteN2CutoffWeights_19,finiteN2CutoffWeights_19_valid⟩
  · exact ⟨finiteN2CutoffWeights_20,finiteN2CutoffWeights_20_valid⟩
  · exact ⟨finiteN2CutoffWeights_21,finiteN2CutoffWeights_21_valid⟩
  · exact ⟨finiteN2CutoffWeights_22,finiteN2CutoffWeights_22_valid⟩
  · exact ⟨finiteN2CutoffWeights_23,finiteN2CutoffWeights_23_valid⟩
  · exact ⟨finiteN2CutoffWeights_24,finiteN2CutoffWeights_24_valid⟩
  · exact ⟨finiteN2CutoffWeights_25,finiteN2CutoffWeights_25_valid⟩
  · exact ⟨finiteN2CutoffWeights_26,finiteN2CutoffWeights_26_valid⟩
  · exact ⟨finiteN2CutoffWeights_27,finiteN2CutoffWeights_27_valid⟩
  · exact ⟨finiteN2CutoffWeights_28,finiteN2CutoffWeights_28_valid⟩
  · exact ⟨finiteN2CutoffWeights_29,finiteN2CutoffWeights_29_valid⟩
  · exact ⟨finiteN2CutoffWeights_30,finiteN2CutoffWeights_30_valid⟩
  · exact ⟨finiteN2CutoffWeights_31,finiteN2CutoffWeights_31_valid⟩
  · exact ⟨finiteN2CutoffWeights_32,finiteN2CutoffWeights_32_valid⟩
  · exact ⟨finiteN2CutoffWeights_33,finiteN2CutoffWeights_33_valid⟩
  · exact ⟨finiteN2CutoffWeights_34,finiteN2CutoffWeights_34_valid⟩
  · exact ⟨finiteN2CutoffWeights_35,finiteN2CutoffWeights_35_valid⟩
  · exact ⟨finiteN2CutoffWeights_36,finiteN2CutoffWeights_36_valid⟩
  · exact ⟨finiteN2CutoffWeights_37,finiteN2CutoffWeights_37_valid⟩
  · exact ⟨finiteN2CutoffWeights_38,finiteN2CutoffWeights_38_valid⟩
  · exact ⟨finiteN2CutoffWeights_39,finiteN2CutoffWeights_39_valid⟩
  · exact ⟨finiteN2CutoffWeights_40,finiteN2CutoffWeights_40_valid⟩
  · exact ⟨finiteN2CutoffWeights_41,finiteN2CutoffWeights_41_valid⟩
  · exact ⟨finiteN2CutoffWeights_42,finiteN2CutoffWeights_42_valid⟩
  · exact ⟨finiteN2CutoffWeights_43,finiteN2CutoffWeights_43_valid⟩
  · exact ⟨finiteN2CutoffWeights_44,finiteN2CutoffWeights_44_valid⟩
  · exact ⟨finiteN2CutoffWeights_45,finiteN2CutoffWeights_45_valid⟩
  · exact ⟨finiteN2CutoffWeights_46,finiteN2CutoffWeights_46_valid⟩
  · exact ⟨finiteN2CutoffWeights_47,finiteN2CutoffWeights_47_valid⟩
  · exact ⟨finiteN2CutoffWeights_48,finiteN2CutoffWeights_48_valid⟩
  · exact ⟨finiteN2CutoffWeights_49,finiteN2CutoffWeights_49_valid⟩
  · exact ⟨finiteN2CutoffWeights_50,finiteN2CutoffWeights_50_valid⟩
  · exact ⟨finiteN2CutoffWeights_51,finiteN2CutoffWeights_51_valid⟩
  · exact ⟨finiteN2CutoffWeights_52,finiteN2CutoffWeights_52_valid⟩
  · exact ⟨finiteN2CutoffWeights_53,finiteN2CutoffWeights_53_valid⟩
  · exact ⟨finiteN2CutoffWeights_54,finiteN2CutoffWeights_54_valid⟩
  · exact ⟨finiteN2CutoffWeights_55,finiteN2CutoffWeights_55_valid⟩
  · exact ⟨finiteN2CutoffWeights_56,finiteN2CutoffWeights_56_valid⟩

end D1Bound5
end

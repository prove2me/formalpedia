-- Prove2me | solution 1 for D1Bound5.oneSmallCutoffRows_finiteN3BsFixedBound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:50:43.402414+00:00
-- url     : https://prove2.me/submissions/bb22efb4-5e83-4d7a-be9f-8bbfb7f8d886

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FiniteN3FixedHeight_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallN3BsFixedArithmetic_Definitions
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_0_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_10_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_11_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_12_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_13_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_14_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_15_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_16_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_17_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_18_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_19_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_1_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_20_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_21_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_22_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_23_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_24_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_25_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_26_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_27_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_28_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_29_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_2_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_30_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_31_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_32_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_33_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_34_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_35_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_36_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_37_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_38_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_39_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_3_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_40_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_41_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_42_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_43_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_44_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_45_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_46_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_47_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_48_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_49_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_4_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_50_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_51_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_52_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_53_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_54_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_55_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_56_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_5_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_6_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_7_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_8_valid
import Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_9_valid

section
namespace D1Bound5
open QuadInt

/- Exact evaluated N3 coefficient certificates on the bs anchors. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0





































































































































































































































/-- The actual printed fixed-triple rows have verified N3 coefficients
on the bs anchor pair, evaluated before taking norms. -/
theorem _root_.solution (r : OneSmallCutoffRow)
    (hr : r ∈ oneSmallCutoffRows) :
    ∃ w : Fin 3 → Fin 2 → Fin 4 → ℚ,
      FiniteN3FixedBound r.triple.anchorB r.triple.anchorS r.Mbs w := by
  simp only [oneSmallCutoffRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨finiteN3BsCutoffWeights_0,finiteN3BsCutoffWeights_0_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_1,finiteN3BsCutoffWeights_1_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_2,finiteN3BsCutoffWeights_2_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_3,finiteN3BsCutoffWeights_3_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_4,finiteN3BsCutoffWeights_4_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_5,finiteN3BsCutoffWeights_5_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_6,finiteN3BsCutoffWeights_6_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_7,finiteN3BsCutoffWeights_7_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_8,finiteN3BsCutoffWeights_8_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_9,finiteN3BsCutoffWeights_9_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_10,finiteN3BsCutoffWeights_10_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_11,finiteN3BsCutoffWeights_11_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_12,finiteN3BsCutoffWeights_12_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_13,finiteN3BsCutoffWeights_13_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_14,finiteN3BsCutoffWeights_14_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_15,finiteN3BsCutoffWeights_15_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_16,finiteN3BsCutoffWeights_16_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_17,finiteN3BsCutoffWeights_17_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_18,finiteN3BsCutoffWeights_18_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_19,finiteN3BsCutoffWeights_19_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_20,finiteN3BsCutoffWeights_20_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_21,finiteN3BsCutoffWeights_21_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_22,finiteN3BsCutoffWeights_22_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_23,finiteN3BsCutoffWeights_23_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_24,finiteN3BsCutoffWeights_24_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_25,finiteN3BsCutoffWeights_25_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_26,finiteN3BsCutoffWeights_26_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_27,finiteN3BsCutoffWeights_27_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_28,finiteN3BsCutoffWeights_28_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_29,finiteN3BsCutoffWeights_29_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_30,finiteN3BsCutoffWeights_30_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_31,finiteN3BsCutoffWeights_31_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_32,finiteN3BsCutoffWeights_32_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_33,finiteN3BsCutoffWeights_33_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_34,finiteN3BsCutoffWeights_34_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_35,finiteN3BsCutoffWeights_35_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_36,finiteN3BsCutoffWeights_36_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_37,finiteN3BsCutoffWeights_37_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_38,finiteN3BsCutoffWeights_38_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_39,finiteN3BsCutoffWeights_39_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_40,finiteN3BsCutoffWeights_40_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_41,finiteN3BsCutoffWeights_41_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_42,finiteN3BsCutoffWeights_42_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_43,finiteN3BsCutoffWeights_43_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_44,finiteN3BsCutoffWeights_44_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_45,finiteN3BsCutoffWeights_45_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_46,finiteN3BsCutoffWeights_46_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_47,finiteN3BsCutoffWeights_47_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_48,finiteN3BsCutoffWeights_48_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_49,finiteN3BsCutoffWeights_49_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_50,finiteN3BsCutoffWeights_50_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_51,finiteN3BsCutoffWeights_51_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_52,finiteN3BsCutoffWeights_52_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_53,finiteN3BsCutoffWeights_53_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_54,finiteN3BsCutoffWeights_54_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_55,finiteN3BsCutoffWeights_55_valid⟩
  · exact ⟨finiteN3BsCutoffWeights_56,finiteN3BsCutoffWeights_56_valid⟩

end D1Bound5
end

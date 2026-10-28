-- Prove2me | solution 1 for D1Bound5.oneSmallCutoffRows_finiteN3AbFixedBound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:50:45.89225+00:00
-- url     : https://prove2.me/submissions/9afcabb3-64f2-4cf8-a274-f3b60b411d49

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
import Definitions.Def_D1Bound5_OneSmallN3AbFixedArithmetic_Definitions
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_0_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_10_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_11_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_12_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_13_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_14_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_15_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_16_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_17_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_18_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_19_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_1_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_20_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_21_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_22_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_23_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_24_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_25_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_26_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_27_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_28_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_29_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_2_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_30_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_31_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_32_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_33_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_34_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_35_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_36_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_37_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_38_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_39_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_3_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_40_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_41_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_42_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_43_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_44_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_45_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_46_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_47_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_48_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_49_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_4_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_50_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_51_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_52_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_53_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_54_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_55_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_56_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_5_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_6_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_7_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_8_valid
import Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_9_valid

section
namespace D1Bound5
open QuadInt

/- Exact evaluated N3 coefficient certificates on the ab anchors. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0





































































































































































































































/-- The actual printed fixed-triple rows have verified N3 coefficients
on the ab anchor pair, evaluated before taking norms. -/
theorem _root_.solution (r : OneSmallCutoffRow)
    (hr : r ∈ oneSmallCutoffRows) :
    ∃ w : Fin 3 → Fin 2 → Fin 4 → ℚ,
      FiniteN3FixedBound r.triple.anchorA r.triple.anchorB r.Mn w := by
  simp only [oneSmallCutoffRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨finiteN3AbCutoffWeights_0,finiteN3AbCutoffWeights_0_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_1,finiteN3AbCutoffWeights_1_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_2,finiteN3AbCutoffWeights_2_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_3,finiteN3AbCutoffWeights_3_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_4,finiteN3AbCutoffWeights_4_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_5,finiteN3AbCutoffWeights_5_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_6,finiteN3AbCutoffWeights_6_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_7,finiteN3AbCutoffWeights_7_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_8,finiteN3AbCutoffWeights_8_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_9,finiteN3AbCutoffWeights_9_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_10,finiteN3AbCutoffWeights_10_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_11,finiteN3AbCutoffWeights_11_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_12,finiteN3AbCutoffWeights_12_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_13,finiteN3AbCutoffWeights_13_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_14,finiteN3AbCutoffWeights_14_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_15,finiteN3AbCutoffWeights_15_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_16,finiteN3AbCutoffWeights_16_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_17,finiteN3AbCutoffWeights_17_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_18,finiteN3AbCutoffWeights_18_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_19,finiteN3AbCutoffWeights_19_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_20,finiteN3AbCutoffWeights_20_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_21,finiteN3AbCutoffWeights_21_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_22,finiteN3AbCutoffWeights_22_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_23,finiteN3AbCutoffWeights_23_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_24,finiteN3AbCutoffWeights_24_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_25,finiteN3AbCutoffWeights_25_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_26,finiteN3AbCutoffWeights_26_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_27,finiteN3AbCutoffWeights_27_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_28,finiteN3AbCutoffWeights_28_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_29,finiteN3AbCutoffWeights_29_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_30,finiteN3AbCutoffWeights_30_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_31,finiteN3AbCutoffWeights_31_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_32,finiteN3AbCutoffWeights_32_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_33,finiteN3AbCutoffWeights_33_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_34,finiteN3AbCutoffWeights_34_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_35,finiteN3AbCutoffWeights_35_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_36,finiteN3AbCutoffWeights_36_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_37,finiteN3AbCutoffWeights_37_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_38,finiteN3AbCutoffWeights_38_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_39,finiteN3AbCutoffWeights_39_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_40,finiteN3AbCutoffWeights_40_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_41,finiteN3AbCutoffWeights_41_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_42,finiteN3AbCutoffWeights_42_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_43,finiteN3AbCutoffWeights_43_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_44,finiteN3AbCutoffWeights_44_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_45,finiteN3AbCutoffWeights_45_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_46,finiteN3AbCutoffWeights_46_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_47,finiteN3AbCutoffWeights_47_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_48,finiteN3AbCutoffWeights_48_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_49,finiteN3AbCutoffWeights_49_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_50,finiteN3AbCutoffWeights_50_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_51,finiteN3AbCutoffWeights_51_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_52,finiteN3AbCutoffWeights_52_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_53,finiteN3AbCutoffWeights_53_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_54,finiteN3AbCutoffWeights_54_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_55,finiteN3AbCutoffWeights_55_valid⟩
  · exact ⟨finiteN3AbCutoffWeights_56,finiteN3AbCutoffWeights_56_valid⟩

end D1Bound5
end

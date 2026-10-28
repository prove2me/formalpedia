-- Prove2me | solution 1 for D1Bound5.oneSmallCutoffRows_finiteA4FixedBound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:50:42.514727+00:00
-- url     : https://prove2.me/submissions/6a0ac728-6e0a-4d16-b080-e96a721bd044

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
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FiniteA4FixedHeight_Definitions
import Definitions.Def_D1Bound5_OneSmallA4FixedArithmetic_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_0_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_10_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_11_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_12_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_13_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_14_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_15_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_16_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_17_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_18_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_19_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_1_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_20_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_21_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_22_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_23_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_24_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_25_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_26_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_27_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_28_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_29_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_2_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_30_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_31_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_32_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_33_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_34_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_35_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_36_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_37_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_38_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_39_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_3_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_40_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_41_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_42_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_43_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_44_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_45_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_46_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_47_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_48_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_49_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_4_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_50_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_51_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_52_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_53_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_54_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_55_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_56_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_5_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_6_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_7_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_8_valid
import Theorems.Thm_D1Bound5_finiteA4CutoffWeights_9_valid

section
namespace D1Bound5
open QuadInt

/- Each exact square certificate evaluates the actual divided A4 root
coefficient in the quadratic integer ring before taking its field norm.
It then checks the printed M4 with a strict rational row-sum comparison. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0





































































































































































































































/-- The actual printed fixed-triple rows have verified A4 coefficients. -/
theorem _root_.solution (r : OneSmallCutoffRow)
    (hr : r ∈ oneSmallCutoffRows) :
    ∃ w : Fin 3 → Fin 2 → Fin 5 → ℚ,
      FiniteA4FixedBound r.triple.anchorA r.triple.anchorB r.M4 w := by
  simp only [oneSmallCutoffRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨finiteA4CutoffWeights_0,finiteA4CutoffWeights_0_valid⟩
  · exact ⟨finiteA4CutoffWeights_1,finiteA4CutoffWeights_1_valid⟩
  · exact ⟨finiteA4CutoffWeights_2,finiteA4CutoffWeights_2_valid⟩
  · exact ⟨finiteA4CutoffWeights_3,finiteA4CutoffWeights_3_valid⟩
  · exact ⟨finiteA4CutoffWeights_4,finiteA4CutoffWeights_4_valid⟩
  · exact ⟨finiteA4CutoffWeights_5,finiteA4CutoffWeights_5_valid⟩
  · exact ⟨finiteA4CutoffWeights_6,finiteA4CutoffWeights_6_valid⟩
  · exact ⟨finiteA4CutoffWeights_7,finiteA4CutoffWeights_7_valid⟩
  · exact ⟨finiteA4CutoffWeights_8,finiteA4CutoffWeights_8_valid⟩
  · exact ⟨finiteA4CutoffWeights_9,finiteA4CutoffWeights_9_valid⟩
  · exact ⟨finiteA4CutoffWeights_10,finiteA4CutoffWeights_10_valid⟩
  · exact ⟨finiteA4CutoffWeights_11,finiteA4CutoffWeights_11_valid⟩
  · exact ⟨finiteA4CutoffWeights_12,finiteA4CutoffWeights_12_valid⟩
  · exact ⟨finiteA4CutoffWeights_13,finiteA4CutoffWeights_13_valid⟩
  · exact ⟨finiteA4CutoffWeights_14,finiteA4CutoffWeights_14_valid⟩
  · exact ⟨finiteA4CutoffWeights_15,finiteA4CutoffWeights_15_valid⟩
  · exact ⟨finiteA4CutoffWeights_16,finiteA4CutoffWeights_16_valid⟩
  · exact ⟨finiteA4CutoffWeights_17,finiteA4CutoffWeights_17_valid⟩
  · exact ⟨finiteA4CutoffWeights_18,finiteA4CutoffWeights_18_valid⟩
  · exact ⟨finiteA4CutoffWeights_19,finiteA4CutoffWeights_19_valid⟩
  · exact ⟨finiteA4CutoffWeights_20,finiteA4CutoffWeights_20_valid⟩
  · exact ⟨finiteA4CutoffWeights_21,finiteA4CutoffWeights_21_valid⟩
  · exact ⟨finiteA4CutoffWeights_22,finiteA4CutoffWeights_22_valid⟩
  · exact ⟨finiteA4CutoffWeights_23,finiteA4CutoffWeights_23_valid⟩
  · exact ⟨finiteA4CutoffWeights_24,finiteA4CutoffWeights_24_valid⟩
  · exact ⟨finiteA4CutoffWeights_25,finiteA4CutoffWeights_25_valid⟩
  · exact ⟨finiteA4CutoffWeights_26,finiteA4CutoffWeights_26_valid⟩
  · exact ⟨finiteA4CutoffWeights_27,finiteA4CutoffWeights_27_valid⟩
  · exact ⟨finiteA4CutoffWeights_28,finiteA4CutoffWeights_28_valid⟩
  · exact ⟨finiteA4CutoffWeights_29,finiteA4CutoffWeights_29_valid⟩
  · exact ⟨finiteA4CutoffWeights_30,finiteA4CutoffWeights_30_valid⟩
  · exact ⟨finiteA4CutoffWeights_31,finiteA4CutoffWeights_31_valid⟩
  · exact ⟨finiteA4CutoffWeights_32,finiteA4CutoffWeights_32_valid⟩
  · exact ⟨finiteA4CutoffWeights_33,finiteA4CutoffWeights_33_valid⟩
  · exact ⟨finiteA4CutoffWeights_34,finiteA4CutoffWeights_34_valid⟩
  · exact ⟨finiteA4CutoffWeights_35,finiteA4CutoffWeights_35_valid⟩
  · exact ⟨finiteA4CutoffWeights_36,finiteA4CutoffWeights_36_valid⟩
  · exact ⟨finiteA4CutoffWeights_37,finiteA4CutoffWeights_37_valid⟩
  · exact ⟨finiteA4CutoffWeights_38,finiteA4CutoffWeights_38_valid⟩
  · exact ⟨finiteA4CutoffWeights_39,finiteA4CutoffWeights_39_valid⟩
  · exact ⟨finiteA4CutoffWeights_40,finiteA4CutoffWeights_40_valid⟩
  · exact ⟨finiteA4CutoffWeights_41,finiteA4CutoffWeights_41_valid⟩
  · exact ⟨finiteA4CutoffWeights_42,finiteA4CutoffWeights_42_valid⟩
  · exact ⟨finiteA4CutoffWeights_43,finiteA4CutoffWeights_43_valid⟩
  · exact ⟨finiteA4CutoffWeights_44,finiteA4CutoffWeights_44_valid⟩
  · exact ⟨finiteA4CutoffWeights_45,finiteA4CutoffWeights_45_valid⟩
  · exact ⟨finiteA4CutoffWeights_46,finiteA4CutoffWeights_46_valid⟩
  · exact ⟨finiteA4CutoffWeights_47,finiteA4CutoffWeights_47_valid⟩
  · exact ⟨finiteA4CutoffWeights_48,finiteA4CutoffWeights_48_valid⟩
  · exact ⟨finiteA4CutoffWeights_49,finiteA4CutoffWeights_49_valid⟩
  · exact ⟨finiteA4CutoffWeights_50,finiteA4CutoffWeights_50_valid⟩
  · exact ⟨finiteA4CutoffWeights_51,finiteA4CutoffWeights_51_valid⟩
  · exact ⟨finiteA4CutoffWeights_52,finiteA4CutoffWeights_52_valid⟩
  · exact ⟨finiteA4CutoffWeights_53,finiteA4CutoffWeights_53_valid⟩
  · exact ⟨finiteA4CutoffWeights_54,finiteA4CutoffWeights_54_valid⟩
  · exact ⟨finiteA4CutoffWeights_55,finiteA4CutoffWeights_55_valid⟩
  · exact ⟨finiteA4CutoffWeights_56,finiteA4CutoffWeights_56_valid⟩

end D1Bound5
end

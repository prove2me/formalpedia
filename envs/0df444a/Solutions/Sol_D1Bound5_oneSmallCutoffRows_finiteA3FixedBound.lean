-- Prove2me | solution 1 for D1Bound5.oneSmallCutoffRows_finiteA3FixedBound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:50:46.683254+00:00
-- url     : https://prove2.me/submissions/94c4ac81-8540-4a3e-ac0e-9f44fb85b8d7

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
import Definitions.Def_D1Bound5_FiniteA3FixedHeight_Definitions
import Definitions.Def_D1Bound5_OneSmallA3FixedArithmetic_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_0_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_10_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_11_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_12_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_13_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_14_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_15_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_16_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_17_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_18_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_19_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_1_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_20_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_21_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_22_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_23_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_24_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_25_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_26_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_27_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_28_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_29_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_2_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_30_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_31_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_32_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_33_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_34_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_35_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_36_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_37_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_38_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_39_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_3_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_40_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_41_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_42_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_43_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_44_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_45_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_46_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_47_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_48_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_49_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_4_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_50_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_51_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_52_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_53_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_54_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_55_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_56_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_5_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_6_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_7_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_8_valid
import Theorems.Thm_D1Bound5_finiteA3CutoffWeights_9_valid

section
namespace D1Bound5
open QuadInt

/- Each exact square certificate evaluates the actual divided A3 root
coefficient in the quadratic integer ring before taking its field norm.
It then checks the printed M3 with a strict rational row-sum comparison. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0





































































































































































































































/-- The actual printed fixed-triple rows have verified A3 coefficients. -/
theorem _root_.solution (r : OneSmallCutoffRow)
    (hr : r ∈ oneSmallCutoffRows) :
    ∃ w : Fin 3 → Fin 2 → Fin 4 → ℚ,
      FiniteA3FixedBound r.triple.anchorA r.triple.anchorB r.M3 w := by
  simp only [oneSmallCutoffRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨finiteA3CutoffWeights_0,finiteA3CutoffWeights_0_valid⟩
  · exact ⟨finiteA3CutoffWeights_1,finiteA3CutoffWeights_1_valid⟩
  · exact ⟨finiteA3CutoffWeights_2,finiteA3CutoffWeights_2_valid⟩
  · exact ⟨finiteA3CutoffWeights_3,finiteA3CutoffWeights_3_valid⟩
  · exact ⟨finiteA3CutoffWeights_4,finiteA3CutoffWeights_4_valid⟩
  · exact ⟨finiteA3CutoffWeights_5,finiteA3CutoffWeights_5_valid⟩
  · exact ⟨finiteA3CutoffWeights_6,finiteA3CutoffWeights_6_valid⟩
  · exact ⟨finiteA3CutoffWeights_7,finiteA3CutoffWeights_7_valid⟩
  · exact ⟨finiteA3CutoffWeights_8,finiteA3CutoffWeights_8_valid⟩
  · exact ⟨finiteA3CutoffWeights_9,finiteA3CutoffWeights_9_valid⟩
  · exact ⟨finiteA3CutoffWeights_10,finiteA3CutoffWeights_10_valid⟩
  · exact ⟨finiteA3CutoffWeights_11,finiteA3CutoffWeights_11_valid⟩
  · exact ⟨finiteA3CutoffWeights_12,finiteA3CutoffWeights_12_valid⟩
  · exact ⟨finiteA3CutoffWeights_13,finiteA3CutoffWeights_13_valid⟩
  · exact ⟨finiteA3CutoffWeights_14,finiteA3CutoffWeights_14_valid⟩
  · exact ⟨finiteA3CutoffWeights_15,finiteA3CutoffWeights_15_valid⟩
  · exact ⟨finiteA3CutoffWeights_16,finiteA3CutoffWeights_16_valid⟩
  · exact ⟨finiteA3CutoffWeights_17,finiteA3CutoffWeights_17_valid⟩
  · exact ⟨finiteA3CutoffWeights_18,finiteA3CutoffWeights_18_valid⟩
  · exact ⟨finiteA3CutoffWeights_19,finiteA3CutoffWeights_19_valid⟩
  · exact ⟨finiteA3CutoffWeights_20,finiteA3CutoffWeights_20_valid⟩
  · exact ⟨finiteA3CutoffWeights_21,finiteA3CutoffWeights_21_valid⟩
  · exact ⟨finiteA3CutoffWeights_22,finiteA3CutoffWeights_22_valid⟩
  · exact ⟨finiteA3CutoffWeights_23,finiteA3CutoffWeights_23_valid⟩
  · exact ⟨finiteA3CutoffWeights_24,finiteA3CutoffWeights_24_valid⟩
  · exact ⟨finiteA3CutoffWeights_25,finiteA3CutoffWeights_25_valid⟩
  · exact ⟨finiteA3CutoffWeights_26,finiteA3CutoffWeights_26_valid⟩
  · exact ⟨finiteA3CutoffWeights_27,finiteA3CutoffWeights_27_valid⟩
  · exact ⟨finiteA3CutoffWeights_28,finiteA3CutoffWeights_28_valid⟩
  · exact ⟨finiteA3CutoffWeights_29,finiteA3CutoffWeights_29_valid⟩
  · exact ⟨finiteA3CutoffWeights_30,finiteA3CutoffWeights_30_valid⟩
  · exact ⟨finiteA3CutoffWeights_31,finiteA3CutoffWeights_31_valid⟩
  · exact ⟨finiteA3CutoffWeights_32,finiteA3CutoffWeights_32_valid⟩
  · exact ⟨finiteA3CutoffWeights_33,finiteA3CutoffWeights_33_valid⟩
  · exact ⟨finiteA3CutoffWeights_34,finiteA3CutoffWeights_34_valid⟩
  · exact ⟨finiteA3CutoffWeights_35,finiteA3CutoffWeights_35_valid⟩
  · exact ⟨finiteA3CutoffWeights_36,finiteA3CutoffWeights_36_valid⟩
  · exact ⟨finiteA3CutoffWeights_37,finiteA3CutoffWeights_37_valid⟩
  · exact ⟨finiteA3CutoffWeights_38,finiteA3CutoffWeights_38_valid⟩
  · exact ⟨finiteA3CutoffWeights_39,finiteA3CutoffWeights_39_valid⟩
  · exact ⟨finiteA3CutoffWeights_40,finiteA3CutoffWeights_40_valid⟩
  · exact ⟨finiteA3CutoffWeights_41,finiteA3CutoffWeights_41_valid⟩
  · exact ⟨finiteA3CutoffWeights_42,finiteA3CutoffWeights_42_valid⟩
  · exact ⟨finiteA3CutoffWeights_43,finiteA3CutoffWeights_43_valid⟩
  · exact ⟨finiteA3CutoffWeights_44,finiteA3CutoffWeights_44_valid⟩
  · exact ⟨finiteA3CutoffWeights_45,finiteA3CutoffWeights_45_valid⟩
  · exact ⟨finiteA3CutoffWeights_46,finiteA3CutoffWeights_46_valid⟩
  · exact ⟨finiteA3CutoffWeights_47,finiteA3CutoffWeights_47_valid⟩
  · exact ⟨finiteA3CutoffWeights_48,finiteA3CutoffWeights_48_valid⟩
  · exact ⟨finiteA3CutoffWeights_49,finiteA3CutoffWeights_49_valid⟩
  · exact ⟨finiteA3CutoffWeights_50,finiteA3CutoffWeights_50_valid⟩
  · exact ⟨finiteA3CutoffWeights_51,finiteA3CutoffWeights_51_valid⟩
  · exact ⟨finiteA3CutoffWeights_52,finiteA3CutoffWeights_52_valid⟩
  · exact ⟨finiteA3CutoffWeights_53,finiteA3CutoffWeights_53_valid⟩
  · exact ⟨finiteA3CutoffWeights_54,finiteA3CutoffWeights_54_valid⟩
  · exact ⟨finiteA3CutoffWeights_55,finiteA3CutoffWeights_55_valid⟩
  · exact ⟨finiteA3CutoffWeights_56,finiteA3CutoffWeights_56_valid⟩

end D1Bound5
end

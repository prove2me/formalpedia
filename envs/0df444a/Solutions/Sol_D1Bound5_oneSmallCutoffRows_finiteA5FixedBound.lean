-- Prove2me | solution 1 for D1Bound5.oneSmallCutoffRows_finiteA5FixedBound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:49:38.896301+00:00
-- url     : https://prove2.me/submissions/cbdbcb22-1bcc-401d-ab62-8984121294d6

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
import Definitions.Def_D1Bound5_FiniteA5FixedHeight_Definitions
import Definitions.Def_D1Bound5_OneSmallA5FixedArithmetic_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_0_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_10_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_11_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_12_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_13_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_14_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_15_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_16_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_17_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_18_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_19_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_1_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_20_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_21_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_22_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_23_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_24_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_25_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_26_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_27_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_28_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_29_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_2_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_30_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_31_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_32_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_33_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_34_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_35_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_36_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_37_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_38_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_39_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_3_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_40_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_41_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_42_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_43_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_44_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_45_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_46_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_47_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_48_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_49_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_4_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_50_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_51_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_52_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_53_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_54_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_55_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_56_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_5_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_6_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_7_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_8_valid
import Theorems.Thm_D1Bound5_finiteA5CutoffWeights_9_valid

section
namespace D1Bound5
open QuadInt

/- Each exact square certificate evaluates the actual divided A5 root
coefficient in the quadratic integer ring before taking its field norm.
It then checks the printed M5 with a strict rational row-sum comparison. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0





































































































































































































































/-- The actual printed fixed-triple rows have verified A5 coefficients. -/
theorem _root_.solution (r : OneSmallCutoffRow)
    (hr : r ∈ oneSmallCutoffRows) :
    ∃ w : Fin 3 → Fin 2 → Fin 6 → ℚ,
      FiniteA5FixedBound r.triple.anchorA r.triple.anchorB r.M5 w := by
  simp only [oneSmallCutoffRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨finiteA5CutoffWeights_0,finiteA5CutoffWeights_0_valid⟩
  · exact ⟨finiteA5CutoffWeights_1,finiteA5CutoffWeights_1_valid⟩
  · exact ⟨finiteA5CutoffWeights_2,finiteA5CutoffWeights_2_valid⟩
  · exact ⟨finiteA5CutoffWeights_3,finiteA5CutoffWeights_3_valid⟩
  · exact ⟨finiteA5CutoffWeights_4,finiteA5CutoffWeights_4_valid⟩
  · exact ⟨finiteA5CutoffWeights_5,finiteA5CutoffWeights_5_valid⟩
  · exact ⟨finiteA5CutoffWeights_6,finiteA5CutoffWeights_6_valid⟩
  · exact ⟨finiteA5CutoffWeights_7,finiteA5CutoffWeights_7_valid⟩
  · exact ⟨finiteA5CutoffWeights_8,finiteA5CutoffWeights_8_valid⟩
  · exact ⟨finiteA5CutoffWeights_9,finiteA5CutoffWeights_9_valid⟩
  · exact ⟨finiteA5CutoffWeights_10,finiteA5CutoffWeights_10_valid⟩
  · exact ⟨finiteA5CutoffWeights_11,finiteA5CutoffWeights_11_valid⟩
  · exact ⟨finiteA5CutoffWeights_12,finiteA5CutoffWeights_12_valid⟩
  · exact ⟨finiteA5CutoffWeights_13,finiteA5CutoffWeights_13_valid⟩
  · exact ⟨finiteA5CutoffWeights_14,finiteA5CutoffWeights_14_valid⟩
  · exact ⟨finiteA5CutoffWeights_15,finiteA5CutoffWeights_15_valid⟩
  · exact ⟨finiteA5CutoffWeights_16,finiteA5CutoffWeights_16_valid⟩
  · exact ⟨finiteA5CutoffWeights_17,finiteA5CutoffWeights_17_valid⟩
  · exact ⟨finiteA5CutoffWeights_18,finiteA5CutoffWeights_18_valid⟩
  · exact ⟨finiteA5CutoffWeights_19,finiteA5CutoffWeights_19_valid⟩
  · exact ⟨finiteA5CutoffWeights_20,finiteA5CutoffWeights_20_valid⟩
  · exact ⟨finiteA5CutoffWeights_21,finiteA5CutoffWeights_21_valid⟩
  · exact ⟨finiteA5CutoffWeights_22,finiteA5CutoffWeights_22_valid⟩
  · exact ⟨finiteA5CutoffWeights_23,finiteA5CutoffWeights_23_valid⟩
  · exact ⟨finiteA5CutoffWeights_24,finiteA5CutoffWeights_24_valid⟩
  · exact ⟨finiteA5CutoffWeights_25,finiteA5CutoffWeights_25_valid⟩
  · exact ⟨finiteA5CutoffWeights_26,finiteA5CutoffWeights_26_valid⟩
  · exact ⟨finiteA5CutoffWeights_27,finiteA5CutoffWeights_27_valid⟩
  · exact ⟨finiteA5CutoffWeights_28,finiteA5CutoffWeights_28_valid⟩
  · exact ⟨finiteA5CutoffWeights_29,finiteA5CutoffWeights_29_valid⟩
  · exact ⟨finiteA5CutoffWeights_30,finiteA5CutoffWeights_30_valid⟩
  · exact ⟨finiteA5CutoffWeights_31,finiteA5CutoffWeights_31_valid⟩
  · exact ⟨finiteA5CutoffWeights_32,finiteA5CutoffWeights_32_valid⟩
  · exact ⟨finiteA5CutoffWeights_33,finiteA5CutoffWeights_33_valid⟩
  · exact ⟨finiteA5CutoffWeights_34,finiteA5CutoffWeights_34_valid⟩
  · exact ⟨finiteA5CutoffWeights_35,finiteA5CutoffWeights_35_valid⟩
  · exact ⟨finiteA5CutoffWeights_36,finiteA5CutoffWeights_36_valid⟩
  · exact ⟨finiteA5CutoffWeights_37,finiteA5CutoffWeights_37_valid⟩
  · exact ⟨finiteA5CutoffWeights_38,finiteA5CutoffWeights_38_valid⟩
  · exact ⟨finiteA5CutoffWeights_39,finiteA5CutoffWeights_39_valid⟩
  · exact ⟨finiteA5CutoffWeights_40,finiteA5CutoffWeights_40_valid⟩
  · exact ⟨finiteA5CutoffWeights_41,finiteA5CutoffWeights_41_valid⟩
  · exact ⟨finiteA5CutoffWeights_42,finiteA5CutoffWeights_42_valid⟩
  · exact ⟨finiteA5CutoffWeights_43,finiteA5CutoffWeights_43_valid⟩
  · exact ⟨finiteA5CutoffWeights_44,finiteA5CutoffWeights_44_valid⟩
  · exact ⟨finiteA5CutoffWeights_45,finiteA5CutoffWeights_45_valid⟩
  · exact ⟨finiteA5CutoffWeights_46,finiteA5CutoffWeights_46_valid⟩
  · exact ⟨finiteA5CutoffWeights_47,finiteA5CutoffWeights_47_valid⟩
  · exact ⟨finiteA5CutoffWeights_48,finiteA5CutoffWeights_48_valid⟩
  · exact ⟨finiteA5CutoffWeights_49,finiteA5CutoffWeights_49_valid⟩
  · exact ⟨finiteA5CutoffWeights_50,finiteA5CutoffWeights_50_valid⟩
  · exact ⟨finiteA5CutoffWeights_51,finiteA5CutoffWeights_51_valid⟩
  · exact ⟨finiteA5CutoffWeights_52,finiteA5CutoffWeights_52_valid⟩
  · exact ⟨finiteA5CutoffWeights_53,finiteA5CutoffWeights_53_valid⟩
  · exact ⟨finiteA5CutoffWeights_54,finiteA5CutoffWeights_54_valid⟩
  · exact ⟨finiteA5CutoffWeights_55,finiteA5CutoffWeights_55_valid⟩
  · exact ⟨finiteA5CutoffWeights_56,finiteA5CutoffWeights_56_valid⟩

end D1Bound5
end

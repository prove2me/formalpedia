-- Prove2me | solution 1 for D1Bound5.productFive_bilinear_l2_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:55:54.109992+00:00
-- url     : https://prove2.me/submissions/edfcf7bc-a80b-4f98-a63d-7a61dd6691b8

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5





end D1Bound5

open scoped InnerProductSpace

namespace D1Bound5

/-- Complex bilinear Cauchy--Schwarz, with the conjugate used only
inside the Hilbert-space inner product. -/
theorem _root_.solution (v w : Fin 4 → ℂ) :
    ‖v ⬝ᵥ w‖ ≤
      ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin 4))‖ *
      ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 4))‖ := by
  let x : EuclideanSpace ℂ (Fin 4) := WithLp.toLp 2 v
  let y : EuclideanSpace ℂ (Fin 4) := WithLp.toLp 2 (star v)
  have hy : ‖y‖ = ‖x‖ := by
    have hsq : ‖y‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq y, EuclideanSpace.norm_sq_eq x]
      simp [x, y]
    nlinarith only [hsq, norm_nonneg x, norm_nonneg y]
  have hinner : v ⬝ᵥ w =
      inner ℂ y (WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 4)) := by
    change v ⬝ᵥ w = inner ℂ (WithLp.toLp 2 (star v))
      (WithLp.toLp 2 w)
    rw [EuclideanSpace.inner_toLp_toLp]
    simp [dotProduct_comm]
  calc
    ‖v ⬝ᵥ w‖ =
        ‖inner ℂ y (WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 4))‖ :=
          congrArg norm hinner
    _ ≤ ‖y‖ * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 4))‖ :=
          norm_inner_le_norm _ _
    _ = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin 4))‖ *
          ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 4))‖ := by rw [hy]





end D1Bound5
end

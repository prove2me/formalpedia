-- Prove2me | solution 1 for D1Bound5.fiveLastColumn_l2_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:55:53.268845+00:00
-- url     : https://prove2.me/submissions/c99f9cce-7531-40f1-b706-423663cee990

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
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
namespace D1Bound5

















open scoped NumberField
open Module






/-- The last-column entry bounds imply the Euclidean estimates in
(integrated-4); the norm here is explicitly the L2 vector norm. -/
theorem _root_.solution (v : Fin 4 → ℂ)
    (hv : ∀ i, ‖v i - (1/2 : ℂ)‖ < (1/400 : ℝ)) :
    ‖(WithLp.toLp 2 (fun i => v i - (1/2 : ℂ)) : EuclideanSpace ℂ (Fin 4))‖ <
        (1/200 : ℝ) ∧
    ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin 4))‖ < (201/200 : ℝ) := by
  let e : EuclideanSpace ℂ (Fin 4) := WithLp.toLp 2 (fun i => v i - (1/2 : ℂ))
  let z : EuclideanSpace ℂ (Fin 4) := WithLp.toLp 2 (fun _ => (1/2 : ℂ))
  let x : EuclideanSpace ℂ (Fin 4) := WithLp.toLp 2 v
  have hsq (i : Fin 4) : ‖v i - (1/2 : ℂ)‖^2 < (1/400 : ℝ)^2 := by
    have hn := norm_nonneg (v i - (1/2 : ℂ))
    have h := hv i
    nlinarith only [h, hn]
  have hen : ‖e‖^2 = ∑ i : Fin 4, ‖v i - (1/2 : ℂ)‖^2 := by
    simpa [e] using EuclideanSpace.norm_sq_eq e
  have hes : ‖e‖^2 < (1/200 : ℝ)^2 := by
    rw [hen, Fin.sum_univ_four]
    linarith only [hsq 0, hsq 1, hsq 2, hsq 3]
  have he : ‖e‖ < (1/200 : ℝ) := by
    nlinarith only [hes, norm_nonneg e]
  have hzsq : ‖z‖^2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq z, Fin.sum_univ_four]
    norm_num [z]
  have hz : ‖z‖ = 1 := by nlinarith only [hzsq, norm_nonneg z]
  have hx : x = e + z := by
    ext i
    change v i = (v i - (1/2 : ℂ)) + (1/2 : ℂ)
    ring
  have hxn : ‖x‖ < (201/200 : ℝ) := by
    have hb := norm_add_le e z
    rw [← hx, hz] at hb
    linarith only [hb, he]
  exact ⟨he, hxn⟩

end D1Bound5
end

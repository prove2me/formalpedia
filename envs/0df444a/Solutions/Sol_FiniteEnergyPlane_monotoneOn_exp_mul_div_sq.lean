-- Prove2me | solution 1 for FiniteEnergyPlane.monotoneOn_exp_mul_div_sq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-23T16:07:30.850579+00:00
-- url     : https://prove2.me/submissions/4633aa41-0511-4816-b812-14f3d7b0c060

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv



namespace FiniteEnergyPlane

open Set

/-- Let `I` be differentiable on `(0, S)` with `2 (1 - C s) I(s) ≤ s I'(s)` there. Then
`s ↦ e^{2 C s} I(s) / s²` is nondecreasing on `(0, S)`. -/
theorem monotoneOn_exp_mul_div_sq_aux {I I' : ℝ → ℝ} {C S : ℝ}
    (hI : ∀ s ∈ Ioo 0 S, HasDerivAt I (I' s) s)
    (hineq : ∀ s ∈ Ioo 0 S, 2 * (1 - C * s) * I s ≤ s * I' s) :
    MonotoneOn (fun s => Real.exp (2 * C * s) * I s / s ^ 2) (Ioo 0 S) := by
  have hd : ∀ s ∈ Ioo 0 S, HasDerivAt (fun s => Real.exp (2 * C * s) * I s / s ^ 2)
      (((Real.exp (2 * C * s) * (2 * C) * I s + Real.exp (2 * C * s) * I' s) * s ^ 2 -
        Real.exp (2 * C * s) * I s * (2 * s)) / (s ^ 2) ^ 2) s := by
    intro s hs
    have hs0 : s ≠ 0 := hs.1.ne'
    have he : HasDerivAt (fun s => Real.exp (2 * C * s)) (Real.exp (2 * C * s) * (2 * C)) s := by
      simpa using ((hasDerivAt_id s).const_mul (2 * C)).exp
    have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * s) s := by
      simpa using hasDerivAt_pow 2 s
    exact (he.mul (hI s hs)).div hsq (pow_ne_zero 2 hs0)
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo 0 S)
    (f' := fun s => ((Real.exp (2 * C * s) * (2 * C) * I s + Real.exp (2 * C * s) * I' s) * s ^ 2 -
        Real.exp (2 * C * s) * I s * (2 * s)) / (s ^ 2) ^ 2) ?_ ?_ ?_
  · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioo] at hs
    exact (hd s hs).hasDerivWithinAt
  · intro s hs
    rw [interior_Ioo] at hs
    have hs0 : 0 < s := hs.1
    apply div_nonneg _ (by positivity)
    have h := hineq s hs
    have he := Real.exp_pos (2 * C * s)
    have : 0 ≤ s * I' s + 2 * C * s * I s - 2 * I s := by nlinarith
    have key : (Real.exp (2 * C * s) * (2 * C) * I s + Real.exp (2 * C * s) * I' s) * s ^ 2 -
        Real.exp (2 * C * s) * I s * (2 * s) =
        Real.exp (2 * C * s) * s * (s * I' s + 2 * C * s * I s - 2 * I s) := by ring
    rw [key]
    positivity

end FiniteEnergyPlane

open FiniteEnergyPlane

open Set

theorem solution {I I' : ℝ → ℝ} {C S : ℝ}
    (hI : ∀ s ∈ Ioo 0 S, HasDerivAt I (I' s) s)
    (hineq : ∀ s ∈ Ioo 0 S, 2 * (1 - C * s) * I s ≤ s * I' s) :
    MonotoneOn (fun s => Real.exp (2 * C * s) * I s / s ^ 2) (Ioo 0 S) :=
  monotoneOn_exp_mul_div_sq_aux hI hineq

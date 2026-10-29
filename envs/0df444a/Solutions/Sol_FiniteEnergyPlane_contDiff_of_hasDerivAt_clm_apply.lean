-- Prove2me | solution 1 for FiniteEnergyPlane.contDiff_of_hasDerivAt_clm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-28T23:12:12.563152+00:00
-- url     : https://prove2.me/submissions/d8b07bdc-6338-44a5-b675-501967bd1634

import Mathlib

open scoped ContDiff

/-! Smoothness of solutions of linear ODEs with smooth coefficients. -/


namespace FiniteEnergyPlane

theorem contDiff_of_hasDerivAt_clm_apply_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ → E →L[ℝ] E) (hA : ContDiff ℝ ∞ A) (x : ℝ → E)
    (hx : ∀ t, HasDerivAt x (A t (x t)) t) : ContDiff ℝ ∞ x := by
  have hd : deriv x = fun t => A t (x t) := funext fun t => (hx t).deriv
  have hdiff : Differentiable ℝ x := fun t => (hx t).differentiableAt
  rw [contDiff_infty]
  intro m
  induction m with
  | zero => exact contDiff_zero.2 hdiff.continuous
  | succ m ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨hdiff, fun h => absurd h (by simp), ?_⟩
    rw [hd]
    exact (contDiff_infty.1 hA m).clm_apply ih

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ → E →L[ℝ] E) (hA : ContDiff ℝ ∞ A) (x : ℝ → E)
    (hx : ∀ t, HasDerivAt x (A t (x t)) t) : ContDiff ℝ ∞ x :=
  contDiff_of_hasDerivAt_clm_apply_aux A hA x hx

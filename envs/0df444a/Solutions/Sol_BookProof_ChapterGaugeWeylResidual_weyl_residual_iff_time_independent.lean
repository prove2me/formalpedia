-- Prove2me | solution 1 for BookProof.ChapterGaugeWeylResidual.weyl_residual_iff_time_independent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:41:35.606773+00:00
-- url     : https://prove2.me/submissions/8256a103-248d-4fa0-935c-eb56ac9ef4c9

-- Generated from ChapterGaugeWeylResidual.lean — solution of BookProof.ChapterGaugeWeylResidual.weyl_residual_iff_time_independent
import Mathlib
import Definitions.Def_ChapterGaugeWeylResidual
open BookProof.ChapterGaugeWeylResidual

set_option maxHeartbeats 1000000 in
theorem solution (θ : ℝ → ℝ → ℝ)
    (hθ : ∀ x, Differentiable ℝ (fun s => θ s x)) :
    (∀ t x, dt θ t x = 0) ↔ TimeIndependent θ := by

  constructor
  · intro h t s x
    exact is_const_of_deriv_eq_zero (hθ x) (fun u => h u x) t s
  · intro h t x
    have : (fun s => θ s x) = fun _ => θ t x := funext fun s => h s t x
    simp [dt, this]

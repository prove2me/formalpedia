-- Prove2me | solution 1 for BookProof.ChapterGaugeWeylResidual.weyl_surface_preserved_by_remnant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:41:36.791719+00:00
-- url     : https://prove2.me/submissions/f3244006-75f2-4295-a416-266b10dac42c

-- Generated from ChapterGaugeWeylResidual.lean — solution of BookProof.ChapterGaugeWeylResidual.weyl_surface_preserved_by_remnant
import Mathlib
import Definitions.Def_ChapterGaugeWeylResidual
import Theorems.Thm_BookProof_ChapterGaugeWeylResidual_weyl_residual_iff_time_independent
open BookProof.ChapterGaugeWeylResidual

set_option maxHeartbeats 1000000 in
theorem solution (θ A0 : ℝ → ℝ → ℝ)
    (hθ : ∀ x, Differentiable ℝ (fun s => θ s x)) (hti : TimeIndependent θ)
    (hA0 : A0 = fun _ _ => 0) :
    gaugeA0 θ A0 = fun _ _ => 0 := by

  have h := (weyl_residual_iff_time_independent θ hθ).mpr hti
  funext t x
  simp [gaugeA0, hA0, h t x]

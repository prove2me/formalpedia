-- Prove2me | solution 1 for ConvexOptAlg.FrankWolfe.thm_3_8_init
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-06T13:44:29.351872+00:00
-- url     : https://prove2.me/submissions/06073280-ac27-4026-ba46-7281ce97d338

import Theorems.Thm_ConvexOptAlg_FrankWolfe_eq_3_4

open ConvexOptAlg.FrankWolfe

set_option maxHeartbeats 800000

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (hXc : IsCompact X) (hXconv : Convex ℝ X)
    (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hf : ConvexOn ℝ X f) (hsmooth : IsBetaSmoothNormOn X f f' β)
    (xstar : E) (hxstar : xstar ∈ X) (hopt : ∀ z ∈ X, f xstar ≤ f z)
    (γ : ℕ → ℝ) (hγ1 : γ 1 = 1)
    (x y : ℕ → E) (hrun : IsFrankWolfeRun X f' γ x y) :
    f (x 2) - f xstar ≤ β / 2 * Metric.diam X ^ 2 := by
  have hfirst := hrun.2 1 le_rfl
  have hxy : x 2 = y 1 := by simpa [hγ1] using hfirst.2
  have hupper := (eq_3_4 X hXconv f f' β hf hsmooth
    (y 1) (x 1) hfirst.1.1 hrun.1).2
  have hlower := (eq_3_4 X hXconv f f' β hf hsmooth
    xstar (x 1) hxstar hrun.1).1
  have horacle := hfirst.1.2 xstar hxstar
  have hdist : ‖y 1 - x 1‖ ≤ Metric.diam X := by
    simpa only [dist_eq_norm] using
      Metric.dist_le_diam_of_mem hXc.isBounded hfirst.1.1 hrun.1
  have hsq : ‖y 1 - x 1‖ ^ 2 ≤ Metric.diam X ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) Metric.diam_nonneg).mpr hdist
  have hquad := mul_le_mul_of_nonneg_left hsq
    (div_nonneg hβ (by norm_num : (0 : ℝ) ≤ 2))
  rw [hxy]
  simp only [map_sub] at hupper hlower
  linarith

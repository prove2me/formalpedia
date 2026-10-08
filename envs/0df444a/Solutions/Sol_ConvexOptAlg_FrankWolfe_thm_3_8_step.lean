-- Prove2me | solution 1 for ConvexOptAlg.FrankWolfe.thm_3_8_step
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-06T13:44:26.611983+00:00
-- url     : https://prove2.me/submissions/c7dbb448-65cf-4e8c-b880-6f534b61a2c9

import Theorems.Thm_ConvexOptAlg_FrankWolfe_eq_3_4

open ConvexOptAlg.FrankWolfe

set_option maxHeartbeats 800000

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (hXc : IsCompact X) (hXconv : Convex ℝ X)
    (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hf : ConvexOn ℝ X f) (hsmooth : IsBetaSmoothNormOn X f f' β)
    (xstar : E) (hxstar : xstar ∈ X) (hopt : ∀ z ∈ X, f xstar ≤ f z)
    (γ : ℕ → ℝ) (hγ : ∀ s : ℕ, 1 ≤ s → γ s ∈ Set.Icc (0 : ℝ) 1)
    (x y : ℕ → E) (hrun : IsFrankWolfeRun X f' γ x y)
    (s : ℕ) (hs : 1 ≤ s) :
    f (x (s + 1)) - f xstar ≤
      (1 - γ s) * (f (x s) - f xstar) + β / 2 * γ s ^ 2 * Metric.diam X ^ 2 := by
  have hx (n : ℕ) (hn : 1 ≤ n) : x n ∈ X := by
    induction n, hn using Nat.le_induction with
    | base => exact hrun.1
    | succ n hn ih =>
        rw [(hrun.2 n hn).2]
        exact hXconv ih (hrun.2 n hn).1.1 (sub_nonneg.mpr (hγ n hn).2)
          (hγ n hn).1 (by ring)
  have hupper := (eq_3_4 X hXconv f f' β hf hsmooth
    (x (s + 1)) (x s) (hx _ (by omega)) (hx s hs)).2
  have hlower := (eq_3_4 X hXconv f f' β hf hsmooth
    xstar (x s) hxstar (hx s hs)).1
  have horacle := (hrun.2 s hs).1.2 xstar hxstar
  have hlinear : f' (x s) (y s - x s) ≤ f xstar - f (x s) := by
    simp only [map_sub] at hlower ⊢
    linarith
  have hlinear' := mul_le_mul_of_nonneg_left hlinear (hγ s hs).1
  have hdist : ‖y s - x s‖ ≤ Metric.diam X := by
    simpa only [dist_eq_norm] using
      Metric.dist_le_diam_of_mem hXc.isBounded (hrun.2 s hs).1.1 (hx s hs)
  have hsq : ‖y s - x s‖ ^ 2 ≤ Metric.diam X ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) Metric.diam_nonneg).mpr hdist
  have hquad := mul_le_mul_of_nonneg_left hsq
    (mul_nonneg (div_nonneg hβ (by norm_num : (0 : ℝ) ≤ 2)) (sq_nonneg (γ s)))
  have hmove : x (s + 1) - x s = γ s • (y s - x s) := by
    rw [(hrun.2 s hs).2]
    module
  rw [hmove, map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hγ s hs).1] at hupper
  simp only [smul_eq_mul] at hupper
  nlinarith

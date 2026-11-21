-- Prove2me | solution 1 for AvramDividend.Classical.avram_a26_original_finitecap_caplinear_interior_moving_gaussian_crossing_ae_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T10:06:37.559183+00:00
-- url     : https://prove2.me/submissions/800d0ae0-cb84-476a-91e7-9c4806fbd5cc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB77_original_finitecap_caplinear_payoff_uniform_continuous_on_true_closed_band
import Theorems.Thm_AvramDividend_Classical_avram_ga_a32_compact_translation_vanishing_radius
open Set Filter AvramDividend.Classical
theorem solution
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw_cont : ContinuousOn w (Set.Ici 0))
    (a b r : ℝ) (hr : 0 < r) (hra : r ≤ a) (hab : a ≤ b)
    (y δ : ℕ → ℝ) (hy : ∀ m, y m ∈ Set.Icc a b)
    (hδ : Tendsto δ atTop (nhds (0 : ℝ))) :
    let V : ℝ → ℝ := fun z =>
      if z ≤ c then w z else w c + (z - c)
    Tendsto (fun m => V (y m + δ m) - V (y m))
      atTop (nhds (0 : ℝ))  := by
  dsimp
  let V : ℝ → ℝ := fun z => if z ≤ c then w z else w c + (z - c)
  have hUC : UniformContinuousOn V (Icc 0 (b + r)) := by
    simpa only [V] using
      (avram_gbB77_original_finitecap_caplinear_payoff_uniform_continuous_on_true_closed_band
        w hw_cont c (b + r) hc)
  have hSub : Icc (a - r) (b + r) ⊆ Icc 0 (b + r) := by
    intro z hz
    exact ⟨by linarith [hz.1, hra], hz.2⟩
  have hCont : ContinuousOn V (Icc (a - r) (b + r)) :=
    hUC.continuousOn.mono hSub
  exact avram_ga_a32_compact_translation_vanishing_radius
    V a b r hr hCont y δ hy hδ

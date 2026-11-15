-- Prove2me | solution 1 for AvramDividend.Classical.avram_b108_original_all_negative_cutoff_void_implies_true_jumpfree
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:24:39.023747+00:00
-- url     : https://prove2.me/submissions/3f13f530-611e-439a-85db-199269093e95

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b109_original_no_negative_band_implies_jumpfree_from_spectral_noPos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0)
    (hNoPos : ∀ u : ℝ≥0, s < u → u ≤ t →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ 0)
    (hNoBand : ∀ n : ℕ, ∀ u : ℝ≥0, s < u → u ≤ t →
      ¬ (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1)))) :
    ∀ u : ℝ≥0, s < u → u ≤ t →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 := by
  exact avram_b109_original_no_negative_band_implies_jumpfree_from_spectral_noPos
    X ω s t hNoBand

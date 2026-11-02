-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_original_zero_cap_chronological_stopped_terminal_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:11:39.217995+00:00
-- url     : https://prove2.me/submissions/1ea12287-2298-45e6-867a-93abe4c0a741

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- At the true finite stop, take the post-right-payment terminal state only
    on paid clocks (including zero), otherwise the original book reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hCzero : C = 0)
    (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0) :
    let τ : ℝ≥0∞ := ruinTime X x D ω
    let θ : ℝ≥0 := (min (T : ℝ≥0∞) τ).toNNReal
    let W : ℝ :=
      if θ = 0 ∨ (T : ℝ≥0∞) < τ then
        x + X.X θ ω - rightLimit D θ ω
      else riskProcess X x D θ ω
    0 ≤ w W := by
  dsimp only
  let τ : ℝ≥0∞ := ruinTime X x D ω
  let θ : ℝ≥0 := (min (T : ℝ≥0∞) τ).toNNReal
  let W : ℝ :=
    if θ = 0 ∨ (T : ℝ≥0∞) < τ then
      x + X.X θ ω - rightLimit D θ ω
    else riskProcess X x D θ ω
  change 0 ≤ w W
  have hcap : ENNReal.ofReal W ≤ C := by
    by_cases hp : θ = 0 ∨ (T : ℝ≥0∞) < τ
    · simpa only [W, if_pos hp] using
        (capped_postPaymentReserve_ofReal_le_cap X x C D hD hxc ω θ)
    · have hθne : θ ≠ 0 := (not_or.mp hp).1
      have hθpos : 0 < θ :=
        lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ θ) (Ne.symm hθne)
      simpa only [W, if_neg hp] using (hD.2 ω θ hθpos)
  have hzero : ENNReal.ofReal W = 0 := by
    apply le_antisymm
    · simpa only [hCzero] using hcap
    · exact (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal W from zero_le)
  have hWle : W ≤ 0 := ENNReal.ofReal_eq_zero.mp hzero
  by_cases hneg : W < 0
  · simpa only [hw_neg W hneg] using (le_refl (0 : ℝ))
  · have hWzero : W = 0 := le_antisymm hWle (le_of_not_gt hneg)
    simpa only [hWzero] using hw0
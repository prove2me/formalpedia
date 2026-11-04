-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_true_clock_eventually_strict_preruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:14:24.829841+00:00
-- url     : https://prove2.me/submissions/915471d5-4fd3-4aeb-9e83-0bbe74132a7c

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Filter.AtTopBot.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_ubv_original_deterministic_bounded_ruin_stopping_package
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Any original pre-ruin time eventually lies strictly inside all truncated clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω) :
    ∀ᶠ n : ℕ in atTop,
      (t : ℝ≥0∞) < min (ruinTime X x D ω) (n : ℝ≥0∞) := by
  have hPack :=
    avram_wave6_ubv_original_deterministic_bounded_ruin_stopping_package
      X x C D hD
  have hSup := hPack.2.2.2 ω
  have hlt : (t : ℝ≥0∞) <
      (⨆ n : ℕ, min (ruinTime X x D ω) (n : ℝ≥0∞)) := by
    simpa only [hSup] using ht
  obtain ⟨k, hk⟩ := lt_iSup_iff.mp hlt
  filter_upwards [Filter.eventually_ge_atTop k] with n hn
  exact lt_of_lt_of_le hk ((hPack.2.2.1 ω) hn)

-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top11_original_zero_nu_path_continuous_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T11:13:50.537182+00:00
-- url     : https://prove2.me/submissions/7952a3c3-3adc-4d5e-8003-13f8434c9bba

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_zero_nu_all_natural_band_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_source_nonjump_iff_continuous_at
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_jump_threshold_iff_leftLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-! The original zero-jump Lévy sample path is continuous at every positive
time on one common full-measure event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      ContinuousAt (fun s : ℝ≥0 => X.X s ω) t := by
  filter_upwards [avram_ubv_top11_zero_nu_all_natural_band_ae
    X hNuZero] with ω hNo
  intro t ht
  apply (avram_wave4_04a_actual_source_nonjump_iff_continuous_at
    X ω t ht).mp
  by_contra hmark
  have hnegative : X.X t ω -
      Function.leftLim (fun s : ℝ≥0 => X.X s ω) t < 0 := by
    exact lt_of_le_of_ne
      (avram_wave4_04a_actual_levy_jumpmark_nonpositive X ω t ht) hmark
  let ε : ℝ := Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - X.X t ω
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := exists_nat_gt t
  have hthreshold : X.X t ω + (1 / ((n : ℝ) + 1)) ≤
      Function.leftLim (fun s : ℝ≥0 => X.X s ω) t := by
    dsimp [ε] at hn
    linarith
  have hsource : ∃ l : ℝ,
      Tendsto (fun s : ℝ≥0 => X.X s ω)
        (nhdsWithin t (Iio t)) (nhds l) ∧
      X.X t ω + (1 / ((n : ℝ) + 1)) ≤ l :=
    (avram_wave7_06_original_jump_threshold_iff_leftLim
      X ω t ht n).2 hthreshold
  exact (hNo N n) ⟨t, ht, hN, hsource⟩

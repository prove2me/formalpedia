-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_separated_negative_band_quadratic_energy_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:05:25.438582+00:00
-- url     : https://prove2.me/submissions/66414d1d-82c5-45b9-97c1-2eb44612d844

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_band_squared_kernel_lintegral_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original separated negative-band quadratic jump energy is finite at every bounded reserve level. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (K : ℝ) (hK : 0 ≤ K)
    (ε : ℝ) (hε : 0 < ε)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hBsep : B ⊆ Iic (-ε)) :
    ∀ u : ℝ, u ≤ K →
      (∫⁻ z in B, ENNReal.ofReal ((w (u + z) - w u) ^ 2) ∂X.ν) < ⊤ := by
  obtain ⟨A, hA, hEnvelope⟩ :=
    avram_p4_f3_original_negative_band_squared_kernel_lintegral_bound
      X w hw_cont hw_neg K hK
  have hνfinite : X.ν B < ⊤ :=
    avram_p2_a_zero_rate_separated_borel_nu_finite
      X B hB ε hε hBsep
  have hBneg : B ⊆ Iic (0 : ℝ) := by
    intro z hz
    have hzle : z ≤ -ε := hBsep hz
    change z ≤ 0
    linarith
  intro u hu
  have hEnergy :=
    hEnvelope u hu B hB hBneg
  exact lt_of_le_of_lt hEnergy
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hνfinite)

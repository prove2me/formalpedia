-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_separated_negative_band_L1_jump_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:05:34.4588+00:00
-- url     : https://prove2.me/submissions/4777b504-16d7-4fb3-96a1-f3c09a614321

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_tail_global_value_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original physical jump coefficient is absolutely Levy-integrable on separated negative bands. -/
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
      (∫⁻ z in B,
        ENNReal.ofReal (|w (u + z) - w u|) ∂X.ν) < ⊤ := by
  obtain ⟨L, hL, hBound⟩ :=
    avram_p4_f3_original_negative_tail_global_value_bound
      w hw_cont hw_neg K hK
  have hνfinite : X.ν B < ⊤ :=
    avram_p2_a_zero_rate_separated_borel_nu_finite
      X B hB ε hε hBsep
  have hBneg : B ⊆ Iic (0 : ℝ) := by
    intro z hz
    have hzle : z ≤ -ε := hBsep hz
    change z ≤ 0
    linarith
  intro u hu
  have hPoint (z : ℝ) (hz : z ∈ B) :
      |w (u + z) - w u| ≤ 2 * L := by
    have hzNonpos : z ≤ 0 := hBneg hz
    have huz : u + z ≤ K := by linarith
    have h1 : |w (u + z)| ≤ L := hBound (u + z) huz
    have h2 : |w u| ≤ L := hBound u hu
    calc
      |w (u + z) - w u| ≤ |w (u + z)| + |w u| := by
        simpa using (abs_sub_le (w (u + z)) (0 : ℝ) (w u))
      _ ≤ 2 * L := by linarith
  calc
    (∫⁻ z in B, ENNReal.ofReal (|w (u + z) - w u|) ∂X.ν)
        ≤ (∫⁻ z in B, ENNReal.ofReal (2 * L) ∂X.ν) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem hB] with z hz
          exact ENNReal.ofReal_le_ofReal (hPoint z hz)
    _ = ENNReal.ofReal (2 * L) * X.ν B := by
          simp [lintegral_const, hB]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hνfinite

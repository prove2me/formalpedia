-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_negative_band_squared_kernel_lintegral_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T16:54:08.514912+00:00
-- url     : https://prove2.me/submissions/64cd97c3-e7f4-4d50-b5b4-020a68fce055

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_tail_global_value_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The squared original negative-jump kernel has a finite-intensity envelope below a fixed reserve ceiling. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u : ℝ, u ≤ K →
      ∀ B : Set ℝ, MeasurableSet B → B ⊆ Iic (0 : ℝ) →
      (∫⁻ z in B, ENNReal.ofReal ((w (u + z) - w u) ^ 2) ∂X.ν) ≤
        ENNReal.ofReal A * X.ν B := by
  obtain ⟨L, hL, hBound⟩ :=
    avram_p4_f3_original_negative_tail_global_value_bound
      w hw_cont hw_neg K hK
  refine ⟨(2 * L) ^ 2, sq_nonneg _, ?_⟩
  intro u hu B hBmeas hB
  have hSq (z : ℝ) (hz : z ∈ B) :
      (w (u + z) - w u) ^ 2 ≤ (2 * L) ^ 2 := by
    have hzNonpos : z ≤ 0 := hB hz
    have huz : u + z ≤ K := by linarith
    have huAbs : |w u| ≤ L := hBound u hu
    have huzAbs : |w (u + z)| ≤ L := hBound (u + z) huz
    have hAbs : |w (u + z) - w u| ≤ 2 * L := by
      calc
        _ ≤ |w (u + z)| + |w u| := by
          simpa using (abs_sub_le (w (u + z)) (0 : ℝ) (w u))
        _ ≤ 2 * L := by linarith
    have hleft := neg_le_of_abs_le hAbs
    have hright := le_of_abs_le hAbs
    have hplus : 0 ≤ 2 * L + (w (u + z) - w u) := by linarith
    have hminus : 0 ≤ 2 * L - (w (u + z) - w u) := by linarith
    nlinarith [mul_nonneg hplus hminus]
  calc
    (∫⁻ z in B, ENNReal.ofReal ((w (u + z) - w u) ^ 2) ∂X.ν)
        ≤ (∫⁻ z in B, ENNReal.ofReal ((2 * L) ^ 2) ∂X.ν) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem hBmeas] with z hz
          exact ENNReal.ofReal_le_ofReal (hSq z hz)
    _ = ENNReal.ofReal ((2 * L) ^ 2) * X.ν B := by
          simp [lintegral_const, hBmeas]

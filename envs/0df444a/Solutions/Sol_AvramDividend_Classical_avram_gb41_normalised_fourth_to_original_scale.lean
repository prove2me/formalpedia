-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb41_normalised_fourth_to_original_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:47:14.975956+00:00
-- url     : https://prove2.me/submissions/2f2f33e3-e56d-42db-b6d9-bbc6e4fcc14b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb39_fourth_lintegral_bound_gives_real_integral
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Restore the physical Gaussian scale from a normalised fourth-moment
bound, without introducing an auxiliary stochastic process. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Ω → ℝ) (σ Δ : ℝ) (hσ : 0 < σ)
    (hZ : Measurable Z)
    (hFourth : (∫⁻ ω, ENNReal.ofReal ((Z ω / σ) ^ 4) ∂P) ≤
      ENNReal.ofReal (3 * Δ ^ 2)) :
    Integrable (fun ω => Z ω ^ 4) P ∧
      (∫ ω, Z ω ^ 4 ∂P) ≤ 3 * σ ^ 4 * Δ ^ 2 := by
  have hNorm : Measurable (fun ω => Z ω / σ) := hZ.div_const σ
  obtain ⟨hI, hB⟩ :=
    avram_gb39_fourth_lintegral_bound_gives_real_integral
      P (fun ω => Z ω / σ) hNorm (3 * Δ ^ 2)
      (by positivity) hFourth
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  have hScale (ω : Ω) :
      Z ω ^ 4 = σ ^ 4 * (Z ω / σ) ^ 4 := by
    field_simp [hσ0]
    <;> ring
  have hScaleFun : (fun ω => Z ω ^ 4) =
      (fun ω => σ ^ 4 * (Z ω / σ) ^ 4) := funext hScale
  constructor
  · rw [hScaleFun]
    exact hI.const_mul _
  · calc
      (∫ ω, Z ω ^ 4 ∂P) =
          σ ^ 4 * (∫ ω, (Z ω / σ) ^ 4 ∂P) := by
            simp only [hScaleFun, integral_const_mul]
      _ ≤ σ ^ 4 * (3 * Δ ^ 2) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
      _ = 3 * σ ^ 4 * Δ ^ 2 := by ring

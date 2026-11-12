-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb42_bounded_original_gaussian_quadratic_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:56:30.186791+00:00
-- url     : https://prove2.me/submissions/5a468512-c237-4f9a-a6c0-2d88e93dc1a5

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb38_bounded_quadratic_fourth_to_integrable_square
import Theorems.Thm_AvramDividend_Classical_avram_gb41_normalised_fourth_to_original_scale
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- One original centred-square cell has second moment proportional to
mesh squared whenever its actual normalised increment has a fourth moment. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H Z : Ω → ℝ) (σ Δ KH : ℝ) (hσ : 0 < σ) (hKH : 0 ≤ KH)
    (hHm : Measurable H) (hHb : ∀ ω, |H ω| ≤ KH)
    (hZm : Measurable Z)
    (hFourth : (∫⁻ ω, ENNReal.ofReal ((Z ω / σ) ^ 4) ∂P) ≤
      ENNReal.ofReal (3 * Δ ^ 2)) :
    Integrable (fun ω => (H ω * (Z ω ^ 2 - Δ * σ ^ 2)) ^ 2) P ∧
      (∫ ω, (H ω * (Z ω ^ 2 - Δ * σ ^ 2)) ^ 2 ∂P) ≤
        8 * KH ^ 2 * σ ^ 4 * Δ ^ 2 := by
  obtain ⟨hZ4, hZ4bound⟩ :=
    avram_gb41_normalised_fourth_to_original_scale
      P Z σ Δ hσ hZm hFourth
  obtain ⟨hI, hB⟩ :=
    avram_gb38_bounded_quadratic_fourth_to_integrable_square
      P H Z (Δ * σ ^ 2) (3 * σ ^ 4 * Δ ^ 2) KH
      hHm hZm hKH hHb hZ4 hZ4bound
  refine ⟨hI, ?_⟩
  calc
    (∫ ω, (H ω * (Z ω ^ 2 - Δ * σ ^ 2)) ^ 2 ∂P) ≤
        2 * KH ^ 2 * (3 * σ ^ 4 * Δ ^ 2 +
          (Δ * σ ^ 2) ^ 2) := hB
    _ = 8 * KH ^ 2 * σ ^ 4 * Δ ^ 2 := by ring

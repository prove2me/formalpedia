-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_turn2_physical_pair_l1_of_exact_ennreal_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:50:30.846257+00:00
-- url     : https://prove2.me/submissions/9cfbff80-1c66-498a-b762-0d3234c34715

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_pair_card_real_measurable_from_intrinsic
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_pair_ennreal_to_real_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let K : Ω → ℝ≥0∞ := fun ω =>
      ((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℕ) : ℝ≥0∞)
    let r : ℝ := (((T : ℝ≥0∞) *
      X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)
    (∫⁻ ω, K ω ∂P) = ENNReal.ofReal (r ^ 2 / 2) →
    Integrable (fun ω => 2 * (K ω).toReal) P ∧
      (∫ ω, 2 * (K ω).toReal ∂P) = r ^ 2 := by
  classical
  dsimp only
  intro hMean
  let F : Ω → Finset ℝ≥0 := fun ω =>
    (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
  let K₀ : Ω → ℕ := fun ω =>
    ((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card
  let K : Ω → ℝ≥0∞ := fun ω => (K₀ ω : ℝ≥0∞)
  have hReal : Measurable (fun ω => (K₀ ω : ℝ)) := by
    exact avram_p4_f_assembly_original_pair_card_real_measurable_from_intrinsic X T n
  have hMeas : Measurable K := by
    have hOf : Measurable (fun ω => ENNReal.ofReal (K₀ ω : ℝ)) :=
      ENNReal.measurable_ofReal.comp hReal
    have hEq : (fun ω => ENNReal.ofReal (K₀ ω : ℝ)) = K := by
      funext ω
      simp [K]
    rw [← hEq]
    exact hOf
  exact avram_p4_f_assembly_original_pair_ennreal_to_real_L1
    X T n hMeas.aemeasurable hMean

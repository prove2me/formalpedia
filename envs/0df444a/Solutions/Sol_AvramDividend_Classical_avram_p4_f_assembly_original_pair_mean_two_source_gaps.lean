-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_pair_mean_two_source_gaps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:02:53.470378+00:00
-- url     : https://prove2.me/submissions/cf2666fd-4894-4377-b775-88bf1071f1e4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_pair_mean_from_grid
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_chronological_pair_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Reduce the original factorial pair mean to measurable grid counts and their actual source expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let A : ℕ → Ω → ℝ≥0∞ := fun k ω =>
      ((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
          Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℕ) : ℝ≥0∞)
    let r : ℝ :=
      (((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)
    (∀ k, Measurable (A k)) →
    Tendsto (fun k => ∫⁻ ω, A k ω ∂P) atTop (𝓝 (ENNReal.ofReal (r ^ 2 / 2))) →
    Integrable (fun ω =>
      2 * (((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℝ)) P ∧
    (∫ ω, 2 * (((F ω ×ˢ F ω).filter
      (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℝ) ∂P) = r ^ 2 := by
  classical
  dsimp only
  intro hAmeas hlimit
  have hKmeas : AEMeasurable
      (fun ω : Ω =>
        (((((avram_wave7_06_original_negative_band_marked_times_finite
          X ω T n).toFinset ×ˢ
          (avram_wave7_06_original_negative_band_marked_times_finite
          X ω T n).toFinset).filter
          (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℕ) : ℝ≥0∞)) P :=
    (avram_p4_f_assembly_original_chronological_pair_measurable X T n).aemeasurable
  exact avram_p4_f_assembly_original_pair_mean_from_grid
    X T hT n hAmeas hKmeas hlimit

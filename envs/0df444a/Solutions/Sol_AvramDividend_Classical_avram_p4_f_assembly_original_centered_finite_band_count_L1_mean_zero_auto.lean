-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_centered_finite_band_count_L1_mean_zero_auto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:40:32.995113+00:00
-- url     : https://prove2.me/submissions/06acb1b3-fd21-4234-a1b7-4656abe1d38e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_L1_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_real_mean_auto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let J : Ω → ℝ := fun ω =>
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal
    let r : ℝ :=
      (((T : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => J ω - r) P ∧
      (∫ ω, J ω - r ∂P) = 0 := by
  dsimp only
  let J : Ω → ℝ := fun ω =>
    (((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal
  let r : ℝ :=
    (((T : ℝ≥0) : ℝ≥0∞) *
      X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
  change Integrable (fun ω => J ω - r) P ∧ (∫ ω, J ω - r ∂P) = 0
  have hJ : Integrable J P :=
    avram_p4_f_assembly_original_cutoff_marked_count_L1_auto X T n
  have hMean : (∫ ω, J ω ∂P) = r :=
    avram_p4_f_assembly_original_cutoff_marked_count_real_mean_auto X T n
  refine ⟨hJ.sub (integrable_const r), ?_⟩
  rw [integral_sub hJ (integrable_const r)]
  simp [hMean]

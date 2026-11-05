-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_zero_horizon_pair_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:42:02.427368+00:00
-- url     : https://prove2.me/submissions/999db04b-9b49-402c-9f8b-cc770bf6dca9

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω 0 n).toFinset
    let K : Ω → ℕ := fun ω =>
      ((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card
    let r : ℝ :=
      ((((0 : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)
    Integrable (fun ω => 2 * (K ω : ℝ)) P ∧
    (∫ ω, 2 * (K ω : ℝ) ∂P) = r ^ 2 := by
  classical
  have hF (ω : Ω) :
      (avram_wave7_06_original_negative_band_marked_times_finite
        X ω 0 n).toFinset = ∅ := by
    ext u
    constructor
    · intro hu
      exfalso
      have hu' :
          u ∈ {v : ℝ≥0 | 0 < v ∧ v ≤ (0 : ℝ≥0) ∧
            X.X v ω - Function.leftLim (fun y : ℝ≥0 => X.X y ω) v ≤
              -(1 / ((n : ℝ) + 1))} := by
        simpa only [Set.Finite.mem_toFinset] using hu
      exact (lt_irrefl (0 : ℝ≥0)) (lt_of_lt_of_le hu'.1 hu'.2.1)
    · simp
  dsimp only
  simp only [hF]
  simp

-- Prove2me | solution 2 for AvramDividend.Classical.avram_p4_f_assembly_original_zero_horizon_pair_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:42:46.620918+00:00
-- url     : https://prove2.me/submissions/054b3666-fbf3-4c82-b71e-b94d41482540

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_chronological_pair_zero_horizon

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
  let F : Ω → Finset ℝ≥0 := fun ω =>
    (avram_wave7_06_original_negative_band_marked_times_finite X ω 0 n).toFinset
  let K : Ω → ℕ := fun ω =>
    ((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card
  have hK (ω : Ω) : K ω = 0 := by
    exact avram_p4_f_assembly_original_chronological_pair_zero_horizon X ω n
  have hzero : (fun ω : Ω => 2 * (K ω : ℝ)) = (fun _ : Ω => (0 : ℝ)) := by
    funext ω
    simp [hK ω]
  dsimp only
  constructor
  · change Integrable (fun ω : Ω => 2 * (K ω : ℝ)) P
    rw [hzero]
    simp
  · change (∫ ω, 2 * (K ω : ℝ) ∂P) =
      (((((0 : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)) ^ 2
    rw [hzero]
    simp

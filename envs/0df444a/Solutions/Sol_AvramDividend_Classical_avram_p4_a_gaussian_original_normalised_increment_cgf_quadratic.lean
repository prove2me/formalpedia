-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_original_normalised_increment_cgf_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:30:16.169201+00:00
-- url     : https://prove2.me/submissions/0e639c40-4b11-499b-bd73-c6228e9ff85e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_normalised_increment_mgf_matches_gaussian

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original same-volatility Gaussian increment has quadratic cumulant. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hν : Y.ν = 0) (hσeq : Y.σ = X.σ) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t) (θ : ℝ) (hθ : 0 ≤ θ) :
    ProbabilityTheory.cgf
      (fun ω => ((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c) / X.σ)
      P θ = ((t - s : ℝ≥0) : ℝ) * (θ ^ 2 / 2) := by
  have hMgf :=
    avram_p4_a_gaussian_original_normalised_increment_mgf_matches_gaussian
      X Y hν hσeq hσ s t hst θ hθ
  calc
    _ = Real.log (ProbabilityTheory.mgf id
      (ProbabilityTheory.gaussianReal 0 (t - s)) θ) := by
        simpa only [ProbabilityTheory.cgf] using congrArg Real.log hMgf
    _ = ((t - s : ℝ≥0) : ℝ) * (θ ^ 2 / 2) := by
        rw [ProbabilityTheory.mgf_id_gaussianReal]
        simp
        ring

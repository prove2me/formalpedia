-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_original_normalised_increment_mgf_matches_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:16:41.562011+00:00
-- url     : https://prove2.me/submissions/268d856e-68aa-40a6-967b-efc0277cb4eb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_normalised_mgf_matches_gaussian_real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original zero-jump Gaussian normalised increments match the real Gaussian MGF. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hν : Y.ν = 0) (hσeq : Y.σ = X.σ) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t) (θ : ℝ) (hθ : 0 ≤ θ) :
    ProbabilityTheory.mgf
      (fun ω => ((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c) / X.σ)
      P θ =
        ProbabilityTheory.mgf id
          (ProbabilityTheory.gaussianReal 0 (t - s)) θ := by
  have hMeas : Measurable (fun z : ℝ =>
      (z - ((t - s : ℝ≥0) : ℝ) * Y.c) / X.σ) := by
    fun_prop
  have hId := (Y.stationaryIncrements s t hst).comp hMeas
  calc
    _ = ProbabilityTheory.mgf
        (fun ω => (Y.X (t - s) ω - ((t - s : ℝ≥0) : ℝ) * Y.c) / X.σ)
        P θ := by
          simpa only [Function.comp_def] using
            congrFun (ProbabilityTheory.mgf_congr_identDistrib hId) θ
    _ = ProbabilityTheory.mgf id
          (ProbabilityTheory.gaussianReal 0 (t - s)) θ :=
      avram_p4_a_gaussian_original_normalised_mgf_matches_gaussian_real
        X Y hν hσeq hσ (t - s) θ hθ

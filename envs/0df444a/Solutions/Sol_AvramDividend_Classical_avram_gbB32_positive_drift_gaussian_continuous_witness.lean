-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB32_positive_drift_gaussian_continuous_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T18:51:53.687012+00:00
-- url     : https://prove2.me/submissions/a6a9371b-2263-4f7e-94dc-38e6b1cb33d8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB29_positive_drift_gaussian_sigma1_witness
import Theorems.Thm_AvramDividend_Classical_canonical_drifted_brownian_zero_continuous
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
      Y.c = 2 ∧ Y.σ = 1 ∧ Y.ν = 0 ∧
      (∀ ω, Continuous (fun t : ℝ≥0 => Y.X t ω)) := by 
  obtain ⟨𝓕, Y, hPath, hc, hσ, hν⟩ :=
    avram_gbB29_positive_drift_gaussian_sigma1_witness
  refine ⟨𝓕, Y, hc, hσ, hν, ?_⟩
  intro ω
  have hBrown := (canonical_drifted_brownian_zero_continuous ω).2
  have ht : Continuous (fun t : ℝ≥0 => (t : ℝ)) := by
    fun_prop
  have hShift : Continuous (fun t : ℝ≥0 =>
      (brownian t ω - brownian 0 ω - (t : ℝ)) + 3 * (t : ℝ)) :=
    hBrown.add (continuous_const.mul ht)
  convert hShift using 1
  funext t
  rw [hPath]
  ring

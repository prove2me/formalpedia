-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB29_positive_drift_gaussian_sigma1_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T13:12:50.635625+00:00
-- url     : https://prove2.me/submissions/e8218bad-b342-4c56-b3cc-0e3668231bfc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_concrete_gaussian_levy_source_witness
import Theorems.Thm_AvramDividend_Classical_levy_linear_drift_shift_triplet_preserved_ws01f
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution :
    ∃ (𝓕 : Filtration ℝ≥0
      (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
      (∀ (t : ℝ≥0) (ω : ℝ≥0 → ℝ),
        Y.X t ω = brownian t ω - brownian 0 ω + 2 * (t : ℝ)) ∧
      Y.c = 2 ∧ Y.σ = 1 ∧ Y.ν = 0 := by 
  obtain ⟨𝓕, X, hX, hc, hσ, hν⟩ :=
    avram_wave3_04_concrete_gaussian_levy_source_witness
  obtain ⟨Y, hY, hψ, hYσ, hYν⟩ :=
    levy_linear_drift_shift_triplet_preserved_ws01f X (-3)
  have hYc : Y.c = 2 := by
    have h := hψ 1
    change laplaceExponent Y.c Y.σ Y.ν 1 =
      laplaceExponent X.c X.σ X.ν 1 - (-3) * 1 at h
    simp [laplaceExponent, hYσ, hYν, hσ, hν, hc] at h
    linarith
  refine ⟨𝓕, Y, ?_, hYc, ?_, ?_⟩
  · intro t ω
    rw [hY t ω, congrFun (congrFun hX t) ω]
    ring
  · rw [hYσ, hσ]
  · rw [hYν, hν]

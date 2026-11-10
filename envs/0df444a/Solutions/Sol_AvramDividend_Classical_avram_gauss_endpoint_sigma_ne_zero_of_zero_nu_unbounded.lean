-- Prove2me | solution 1 for AvramDividend.Classical.avram_gauss_endpoint_sigma_ne_zero_of_zero_nu_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T12:50:10.01236+00:00
-- url     : https://prove2.me/submissions/188dba0a-1de6-41cc-831a-e443634f68f9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- In the absence of jumps, unbounded variation requires Gaussian noise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hBV : ¬ X.BoundedVariation) :
    X.σ ≠ 0 := by
  intro hσ
  apply hBV
  change X.σ = 0 ∧
    (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) < ⊤
  refine ⟨hσ, ?_⟩
  simp [hν]

-- Prove2me | solution 1 for AvramDividend.Classical.avram_e0_singular_sigma_zero_bv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:56:53.461563+00:00
-- url     : https://prove2.me/submissions/370719d0-d8e0-4545-8d5f-d6f67ae458a3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gen15_singular_density_bv_lintegral_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Source-exact bounded variation for the singular pure-jump triplet. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : X.σ = 0)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0)) :
    X.BoundedVariation := by
  change X.σ = 0 ∧ (∫⁻ z in Ioo (-1 : ℝ) 0, ENNReal.ofReal |z| ∂X.ν) < ⊤
  refine ⟨hσ, ?_⟩
  rw [hν]
  exact AvramDividend.Classical.avram_gen15_singular_density_bv_lintegral_finite

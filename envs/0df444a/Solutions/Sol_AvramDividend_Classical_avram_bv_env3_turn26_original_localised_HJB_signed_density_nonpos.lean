-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn26_original_localised_HJB_signed_density_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:05:32.497368+00:00
-- url     : https://prove2.me/submissions/8ae98494-78fe-441c-8d4e-247d6bb2a6c9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual original-generator HJB drift density is signed on the localised positive reserve band. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (U : ℝ≥0 × Ω → ℝ) (E : Set (ℝ≥0 × Ω))
    (hInterior : ∀ p ∈ E, 0 < U p ∧ ENNReal.ofReal (U p) < C) :
    ∀ p : ℝ≥0 × Ω,
      (if p ∈ E then
        Real.exp (-(q * (p.1 : ℝ))) *
          (X.generator w (U p) - q * w (U p))
       else 0) ≤ 0 := by
  intro p
  by_cases hp : p ∈ E
  · have hInside := hInterior p hp
    have hGen := (hw_gen (U p) hInside.1 hInside.2).2
    have hExp : 0 ≤ Real.exp (-(q * (p.1 : ℝ))) :=
      (Real.exp_pos _).le
    simpa only [if_pos hp] using mul_nonpos_of_nonneg_of_nonpos hExp hGen
  · simp only [if_neg hp, le_refl]

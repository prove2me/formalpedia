-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB32_original_gaussian_caplinear_upper_generator_eq_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:43:34.821961+00:00
-- url     : https://prove2.me/submissions/aa0c896d-c5cd-4163-a5ee-f561035d4d46

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_zerojump_local_affine_jet_generator_drift
import Theorems.Thm_AvramDividend_Classical_avram_gbB31_interior_caplinear_affine_upper_derivatives
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (w : ℝ → ℝ) (b y : ℝ) (hy : b < y) :
    let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
    X.GeneratorIntegrable V y ∧ X.generator V y = X.c := by
  let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
  obtain ⟨hfirst, hsecond⟩ :=
    avram_gbB31_interior_caplinear_affine_upper_derivatives w b y hy
  exact avram_gbB30_zerojump_local_affine_jet_generator_drift
    X hν V y hfirst hsecond

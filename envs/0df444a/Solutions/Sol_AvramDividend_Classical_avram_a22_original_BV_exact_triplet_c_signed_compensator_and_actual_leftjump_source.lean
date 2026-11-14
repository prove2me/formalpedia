-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_original_BV_exact_triplet_c_signed_compensator_and_actual_leftjump_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T21:25:01.106965+00:00
-- url     : https://prove2.me/submissions/ca539679-8d0e-4d40-af52-97942b2a2fb8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux11_original_BV_raw_removed_residual_zero_ae
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_BV_drift_minus_triplet_c_exact_smallnegative_compensator
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The true original BV Lévy path is triplet drift minus strict negative compensator and its physical jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω = (t : ℝ) * X.c -
        (t : ℝ) * (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω else 0) := by
  have hPath := avram_redux11_original_BV_raw_removed_residual_zero_ae X hX hBV
  have hTriplet :=
    avram_a22_original_BV_drift_minus_triplet_c_exact_smallnegative_compensator X
  filter_upwards [hPath] with ω hω
  intro t
  have ht := hω t
  have hDriftScaled :
      (t : ℝ) * (X.drift - X.c) =
      -(t : ℝ) * (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) := by
    rw [hTriplet]
    ring
  nlinarith only [ht, hDriftScaled]

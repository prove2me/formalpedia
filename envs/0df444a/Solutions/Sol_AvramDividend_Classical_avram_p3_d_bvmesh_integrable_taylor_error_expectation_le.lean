-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_d_bvmesh_integrable_taylor_error_expectation_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:06:38.900574+00:00
-- url     : https://prove2.me/submissions/795c9178-e9bb-4e88-a836-aae349aec05b

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- An a.e. pathwise BV Taylor error with an integrable envelope yields an
explicit L1 expectation error; no stopping-time assertion is used. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (err B : Ω → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (herr : Integrable err P) (hB : Integrable B P)
    (hbound : ∀ᵐ ω ∂P, |err ω| ≤ ε * B ω) :
    (∫ ω, |err ω| ∂P) ≤ ε * (∫ ω, B ω ∂P) := by
  calc
    (∫ ω, |err ω| ∂P) ≤ ∫ ω, ε * B ω ∂P :=
      integral_mono_ae herr.abs (hB.const_mul ε) hbound
    _ = ε * (∫ ω, B ω ∂P) := by
      rw [integral_const_mul]

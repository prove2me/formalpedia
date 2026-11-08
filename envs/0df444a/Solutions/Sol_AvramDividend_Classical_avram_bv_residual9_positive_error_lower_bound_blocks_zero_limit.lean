-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_positive_error_lower_bound_blocks_zero_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:54:01.430939+00:00
-- url     : https://prove2.me/submissions/ef60e4d8-c38f-4038-b4a9-e41cd2e14f2c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

/-- A strictly positive floor is incompatible with convergence to zero. -/
theorem solution
    (ε : ℝ) (hε : 0 < ε) (f : ℕ → ℝ)
    (hbound : ∀ n, ε ≤ f n) :
    ¬ Tendsto f atTop (nhds (0 : ℝ)) := by
  intro h
  have he : ∀ᶠ n : ℕ in atTop, f n < ε :=
    h.eventually (Iio_mem_nhds hε)
  obtain ⟨n, hn⟩ := he.exists
  exact (not_lt_of_ge (hbound n)) hn

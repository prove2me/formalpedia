-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger136_original_gaussian_discounted_physical_cell_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:52:41.542686+00:00
-- url     : https://prove2.me/submissions/aeac66fd-6909-46d8-82fa-98825e99f09c

import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal
noncomputable section

theorem solution
    (q : ℝ) (w : ℝ → ℝ) (s t : ℝ≥0) (y z : ℝ) :
    (Real.exp (-(q * (t : ℝ))) - Real.exp (-(q * (s : ℝ)))) * w y +
    Real.exp (-(q * (t : ℝ))) * (w z - w y) =
    Real.exp (-(q * (t : ℝ))) * w z -
    Real.exp (-(q * (s : ℝ))) * w y := by
  ring

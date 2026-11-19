-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_strict_stopping_clock_has_finite_preruin_buffer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T18:58:16.632139+00:00
-- url     : https://prove2.me/submissions/ebe38c4e-df19-4dbd-810d-8f326f464b07

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (t : ℝ≥0) (R : ℝ≥0∞) (h : (t : ℝ≥0∞) < R) :
    ∃ ρ : ℝ≥0, t < ρ ∧ (ρ : ℝ≥0∞) ≤ R := by
  rcases ENNReal.lt_iff_exists_nnreal_btwn.mp h with ⟨ρ, htρ, hρR⟩
  exact ⟨ρ, ENNReal.coe_lt_coe.mp htρ, le_of_lt hρR⟩

-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger111_subclock_le_ruin_and_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:54:23.382775+00:00
-- url     : https://prove2.me/submissions/a712f90d-1024-4652-ab3e-8662b2f98c65

import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal
noncomputable section

/-- A finite clock no later than a ruin-horizon minimum is below
    both the finite horizon and the original (possibly infinite) ruin. -/
theorem solution
    (σ : ℝ≥0∞) (n ρ : ℝ≥0)
    (hρ : ρ ≤ (min σ (n : ℝ≥0∞)).toNNReal) :
    ρ ≤ n ∧ (ρ : ℝ≥0∞) ≤ σ := by
  have hcast : (ρ : ℝ≥0∞) ≤ min σ (n : ℝ≥0∞) := by
    calc
      (ρ : ℝ≥0∞) ≤
          ((min σ (n : ℝ≥0∞)).toNNReal : ℝ≥0∞) := by
            exact_mod_cast hρ
      _ ≤ min σ (n : ℝ≥0∞) := ENNReal.coe_toNNReal_le_self
  constructor
  · have hn : (ρ : ℝ≥0∞) ≤ (n : ℝ≥0∞) :=
      hcast.trans (min_le_right _ _)
    exact_mod_cast hn
  · exact hcast.trans (min_le_left _ _)

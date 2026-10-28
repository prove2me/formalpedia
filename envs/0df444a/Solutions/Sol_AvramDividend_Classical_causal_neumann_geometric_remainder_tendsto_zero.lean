-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_geometric_remainder_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T13:19:25.247619+00:00
-- url     : https://prove2.me/submissions/ba044770-abcb-4272-9fd1-a2fd3cbc621a

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.Normed.Group.Real

open Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A geometric pointwise majorant forces every Neumann remainder to vanish. -/
theorem solution
    (Q : ℕ → ℝ → ℝ) (C : ℝ → ℝ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hbound : ∀ n : ℕ, ∀ x : ℝ, |Q n x| ≤ C x * ρ ^ n) :
    ∀ x : ℝ, Tendsto (fun n : ℕ => Q n x) atTop (nhds (0 : ℝ)) := by
  intro x
  have hpow : Tendsto (fun n : ℕ => ρ ^ n) atTop (nhds (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
  have hmajor : Tendsto (fun n : ℕ => C x * ρ ^ n)
      atTop (nhds (0 : ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => C x)
        atTop (nhds (C x))).mul hpow
  have habs : Tendsto (fun n : ℕ => |Q n x|)
      atTop (nhds (0 : ℝ)) :=
    squeeze_zero (fun n => abs_nonneg (Q n x))
      (fun n => hbound n x) hmajor
  apply (tendsto_zero_iff_norm_tendsto_zero).2
  simpa only [Real.norm_eq_abs] using habs

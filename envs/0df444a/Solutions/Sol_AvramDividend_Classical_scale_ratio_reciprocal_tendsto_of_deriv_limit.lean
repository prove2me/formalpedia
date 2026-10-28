-- Prove2me | solution 1 for AvramDividend.Classical.scale_ratio_reciprocal_tendsto_of_deriv_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:59:01.692981+00:00
-- url     : https://prove2.me/submissions/4afa796b-7f85-4461-92aa-f26a97f77410

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set

/-- The scale quotient has the expected zero-boundary limit under a nonzero derivative limit. -/
theorem solution
    (W : ℝ → ℝ)
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (d : ℝ) (hd : d ≠ 0)
    (hderiv : Tendsto
      (fun n : ℕ => deriv W (1 / ((n : ℝ) + 1)))
      atTop (nhds d)) :
    Tendsto
      (fun n : ℕ => W (1 / ((n : ℝ) + 1)) /
        deriv W (1 / ((n : ℝ) + 1)))
      atTop (nhds (W 0 / d)) := by
  have hr : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
      atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hrwithin : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
      atTop (nhdsWithin (0 : ℝ) (Ici 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hr, ?_⟩
    exact Filter.Eventually.of_forall (fun n : ℕ => by
      exact le_of_lt (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)))
  have hW : Tendsto (fun n : ℕ => W (1 / ((n : ℝ) + 1)))
      atTop (nhds (W 0)) := hcont.tendsto.comp hrwithin
  exact hW.div hderiv hd

-- Prove2me | solution 1 for AvramDividend.Classical.causal_bcf_banach_contracting_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T23:15:19.122187+00:00
-- url     : https://prove2.me/submissions/7b00dda9-fb02-4dda-85a1-844e681e0d95

import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    (F : BoundedContinuousFunction ℝ≥0 ℝ →
      BoundedContinuousFunction ℝ≥0 ℝ)
    (c : ℝ≥0) (hc : c < 1)
    (hF : ContractingWith c F) :
    ∃ f : BoundedContinuousFunction ℝ≥0 ℝ, F f = f := by
  let x : BoundedContinuousFunction ℝ≥0 ℝ := 0
  obtain ⟨f, hf, _, _⟩ :=
    hF.exists_fixedPoint x (edist_ne_top x (F x))
  exact ⟨f, hf⟩

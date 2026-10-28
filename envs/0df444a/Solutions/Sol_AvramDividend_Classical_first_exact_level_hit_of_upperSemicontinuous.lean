-- Prove2me | solution 1 for AvramDividend.Classical.first_exact_level_hit_of_upperSemicontinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T19:01:10.622194+00:00
-- url     : https://prove2.me/submissions/86b676cb-7595-4291-b95a-6ebd7960ffcc

import Theorems.Thm_AvramDividend_Classical_first_superlevel_hit_of_upperSemicontinuous
import Mathlib.Topology.Semicontinuity.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set Topology
open scoped NNReal

theorem solution
    (R : ℝ≥0 → ℝ) (ζ : ℝ≥0) (x : ℝ)
    (husc : UpperSemicontinuousOn R (Icc 0 ζ))
    (hzero : R 0 = 0) (hx : 0 < x)
    (hBound : ∀ t : ℝ≥0, t ≤ ζ → R t ≤ x)
    (hHit : ∃ t : ℝ≥0, t < ζ ∧ x ≤ R t) :
    ∃ T : ℝ≥0,
      T = sInf (Icc (0 : ℝ≥0) ζ ∩ R ⁻¹' Ici x) ∧
      0 < T ∧ T < ζ ∧ R T = x ∧
      ∀ s : ℝ≥0, s ≤ ζ → R s = x → T ≤ s := by
  obtain ⟨T, hDef, hTpos, hTlt, hTge, hTfirst⟩ :=
    first_superlevel_hit_of_upperSemicontinuous
      R ζ x husc hzero hx hHit
  have hExact : R T = x :=
    le_antisymm (hBound T (le_of_lt hTlt)) hTge
  refine ⟨T, hDef, hTpos, hTlt, hExact, ?_⟩
  intro s hs hEq
  exact hTfirst s hs (le_of_eq hEq.symm)

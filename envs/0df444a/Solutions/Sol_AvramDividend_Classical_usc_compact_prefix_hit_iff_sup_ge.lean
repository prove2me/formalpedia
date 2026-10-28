-- Prove2me | solution 1 for AvramDividend.Classical.usc_compact_prefix_hit_iff_sup_ge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:11:36.386263+00:00
-- url     : https://prove2.me/submissions/33842d6c-28a7-41af-826b-e72a3edc9423

import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_usc_compact_prefix_sup_strictly_below_level

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set Topology
open scoped NNReal

theorem solution
    (R : ℝ≥0 → ℝ) (t : ℝ≥0) (x : ℝ)
    (husc : UpperSemicontinuousOn R (Icc 0 t)) :
    (∃ s : ℝ≥0, s ≤ t ∧ x ≤ R s) ↔
      x ≤ sSup (R '' Icc (0 : ℝ≥0) t) := by
  constructor
  · rintro ⟨s, hs, hlev⟩
    have hbdd : BddAbove (R '' Icc (0 : ℝ≥0) t) :=
      UpperSemicontinuousOn.bddAbove_of_isCompact isCompact_Icc husc
    have hmem : R s ∈ R '' Icc (0 : ℝ≥0) t :=
      ⟨s, ⟨(show (0 : ℝ≥0) ≤ s from zero_le), hs⟩, rfl⟩
    exact hlev.trans (le_csSup hbdd hmem)
  · intro hsup
    by_contra hnone
    have hbelow : ∀ s : ℝ≥0, s ≤ t → R s < x := by
      intro s hs
      by_contra hnlt
      have hge : x ≤ R s := le_of_not_gt hnlt
      exact hnone ⟨s, hs, hge⟩
    have hgap :=
      usc_compact_prefix_sup_strictly_below_level R t x husc hbelow
    exact not_lt_of_ge hsup hgap

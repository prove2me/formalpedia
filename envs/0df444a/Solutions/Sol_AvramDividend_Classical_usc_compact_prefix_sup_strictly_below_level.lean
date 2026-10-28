-- Prove2me | solution 1 for AvramDividend.Classical.usc_compact_prefix_sup_strictly_below_level
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T20:48:41.152814+00:00
-- url     : https://prove2.me/submissions/f7109db8-59e7-4739-8e8f-1b68c2c2d4f7

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set Topology
open scoped NNReal

theorem solution
    (R : ℝ≥0 → ℝ) (t : ℝ≥0) (x : ℝ)
    (husc : UpperSemicontinuousOn R (Icc 0 t))
    (hNoHit : ∀ s : ℝ≥0, s ≤ t → R s < x) :
    sSup (R '' Icc (0 : ℝ≥0) t) < x := by
  have hne : (Icc (0 : ℝ≥0) t).Nonempty :=
    ⟨0, ⟨le_refl 0, (show (0 : ℝ≥0) ≤ t from zero_le)⟩⟩
  obtain ⟨a, ha, hmax⟩ :=
    UpperSemicontinuousOn.exists_isMaxOn hne isCompact_Icc husc
  have himage : (R '' Icc (0 : ℝ≥0) t).Nonempty := by
    refine ⟨R 0, 0, ?_, rfl⟩
    exact ⟨le_refl 0, (show (0 : ℝ≥0) ≤ t from zero_le)⟩
  have hupper : sSup (R '' Icc (0 : ℝ≥0) t) ≤ R a := by
    apply csSup_le himage
    intro y hy
    obtain ⟨s, hs, rfl⟩ := hy
    exact hmax hs
  exact lt_of_le_of_lt hupper (hNoHit a ha.2)

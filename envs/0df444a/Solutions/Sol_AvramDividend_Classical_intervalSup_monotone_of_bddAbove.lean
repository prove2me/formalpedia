-- Prove2me | solution 1 for AvramDividend.Classical.intervalSup_monotone_of_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:30:49.874561+00:00
-- url     : https://prove2.me/submissions/ff5f4510-757c-4a84-b463-7a3bb4cd41a0

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal

/-- Supremum over expanding initial intervals is monotone for a locally bounded path. -/
theorem solution
    (f : ℝ≥0 → ℝ)
    (hb : ∀ t : ℝ≥0, BddAbove (f '' Set.Icc 0 t)) :
    Monotone (fun t : ℝ≥0 => sSup (f '' Set.Icc 0 t)) := by
  intro s t hst
  have hs : (f '' Set.Icc 0 s).Nonempty := by
    exact ⟨f 0, ⟨0, ⟨le_refl (0 : ℝ≥0), zero_le⟩, rfl⟩⟩
  refine csSup_le_csSup (hb t) hs ?_
  rintro y ⟨v, hv, rfl⟩
  exact ⟨v, ⟨hv.1, hv.2.trans hst⟩, rfl⟩

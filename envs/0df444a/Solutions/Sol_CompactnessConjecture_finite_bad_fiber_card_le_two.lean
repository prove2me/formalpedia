-- Prove2me | solution 1 for CompactnessConjecture.finite_bad_fiber_card_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/3e56d6e8-ae6b-4683-ba6e-e5f0bc972070

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {α β : Type*} [Fintype β]
    (fibers : α → Finset β) (good : β → Prop)
    [DecidablePred good]
    (hgood : ∀ (index : α) (vertex : β),
      vertex ∈ fibers index →
      3 ≤ (fibers index).card → good vertex)
    (index : α) :
    ((fibers index).filter fun vertex => ¬ good vertex).card ≤ 2 := by
  classical
  by_cases hlarge : 3 ≤ (fibers index).card
  · have hempty :
        (fibers index).filter (fun vertex => ¬ good vertex) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro vertex hvertex hbad
      exact hbad (hgood index vertex hvertex hlarge)
    simp [hempty]
  · have hcard :=
      Finset.card_filter_le (fibers index)
        (fun vertex => ¬ good vertex)
    omega
end CompactnessConjecture

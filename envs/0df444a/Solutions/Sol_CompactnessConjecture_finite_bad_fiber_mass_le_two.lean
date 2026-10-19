-- Prove2me | solution 1 for CompactnessConjecture.finite_bad_fiber_mass_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/da08054f-e6f6-4110-8e51-a497c2e7ab37

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_finite_bad_fiber_card_le_two

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {α β : Type*} [Fintype α] [Fintype β]
    (fibers : α → Finset β) (good : β → Prop)
    (hgood : ∀ (index : α) (vertex : β),
      vertex ∈ fibers index →
      3 ≤ (fibers index).card → good vertex) :
    finiteBadFiberMass fibers good ≤ 2 * Fintype.card α := by
  classical
  simpa [finiteBadFiberMass, Nat.mul_comm] using
    Finset.sum_le_card_nsmul Finset.univ
      (fun index => ((fibers index).filter fun vertex => ¬ good vertex).card)
      2 (fun index _ => finite_bad_fiber_card_le_two fibers good hgood index)
end CompactnessConjecture

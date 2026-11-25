-- Prove2me | solution 1 for DilworthTheorem.cmin_not_mem_upperCone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:33:24.661037+00:00
-- url     : https://prove2.me/submissions/341e6b00-8816-4e4e-a17c-67f8de142f29

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Antichain
import Mathlib.Tactic
import Definitions.Def_StableMarriageF6_DilworthTheorem

set_option autoImplicit true
open DilworthTheorem
open Finset
open Classical
variable {α : Type*} [PartialOrder α]
namespace DilworthTheorem
theorem _root_.solution {S A C : Finset α} {cmin : α}
    (hAS : A ⊆ S) (hcmin_in : cmin ∈ C) (hcmin_min : ∀ x ∈ S, x ≤ cmin → x = cmin)
    (hAC_disj : Disjoint A C) :
    cmin ∉ upperCone S A := by
  intro h; rw [upperCone, mem_filter] at h; rcases h with ⟨-, a, ha, hle⟩
  exact (disjoint_left.mp hAC_disj ha) (hcmin_min a (hAS ha) hle ▸ hcmin_in)
end DilworthTheorem

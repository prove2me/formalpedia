-- Prove2me | solution 1 for DilworthTheorem.cmax_not_mem_lowerCone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:33:09.925711+00:00
-- url     : https://prove2.me/submissions/83aa82ce-d936-4a94-905c-4d2957c3d0e6

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
theorem _root_.solution {S A C : Finset α} {cmax : α}
    (hAS : A ⊆ S) (hcmax_in : cmax ∈ C) (hcmax_max : ∀ x ∈ S, cmax ≤ x → x = cmax)
    (hAC_disj : Disjoint A C) :
    cmax ∉ lowerCone S A := by
  intro h; rw [lowerCone, mem_filter] at h; rcases h with ⟨-, a, ha, hle⟩
  exact (disjoint_left.mp hAC_disj ha) (hcmax_max a (hAS ha) hle ▸ hcmax_in)
end DilworthTheorem

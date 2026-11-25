-- Prove2me | solution 1 for DilworthTheorem.lowerCone_inter_upperCone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:32:17.222345+00:00
-- url     : https://prove2.me/submissions/7f17d6c6-5958-41d4-8f25-f74da2b96aa7

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
theorem _root_.solution {S A : Finset α} (hA_anti : IsAntichain (A : Set α)) (hAS : A ⊆ S) :
    lowerCone S A ∩ upperCone S A = A := by
  ext x; simp only [mem_inter, lowerCone, upperCone, mem_filter]
  refine ⟨?_, fun hx => ⟨⟨hAS hx, x, hx, le_rfl⟩, ⟨hAS hx, x, hx, le_rfl⟩⟩⟩
  rintro ⟨⟨-, a1, ha1, hx1⟩, ⟨-, a2, ha2, hx2⟩⟩
  have heq : a2 = a1 := by by_contra hne; exact (hA_anti a2 a1 ha2 ha1 hne).1 (hx2.trans hx1)
  subst heq; exact le_antisymm hx1 hx2 ▸ ha1
end DilworthTheorem

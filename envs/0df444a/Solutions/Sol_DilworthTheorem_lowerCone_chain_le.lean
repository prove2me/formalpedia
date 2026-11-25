-- Prove2me | solution 1 for DilworthTheorem.lowerCone_chain_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:34:13.489803+00:00
-- url     : https://prove2.me/submissions/dc5a1e8e-90a3-4a02-b1cc-075ada9a251e

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
theorem _root_.solution {D A : Finset α} {e u : α}
    (hD_chain : IsChain (D : Set α)) (hA_anti : IsAntichain (A : Set α))
    (heD : e ∈ D) (heA : e ∈ A) (huD : u ∈ D) (hu_cone : ∃ a ∈ A, u ≤ a) :
    u ≤ e := by
  rcases hD_chain u e huD heD with hle | hle
  · exact hle
  · rcases hu_cone with ⟨a, ha, hu_le_a⟩
    have : e = a := by by_contra hne; exact (hA_anti e a heA ha hne).1 (hle.trans hu_le_a)
    subst this; exact hu_le_a
end DilworthTheorem

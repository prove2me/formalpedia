-- Prove2me | solution 1 for DilworthTheorem.upperCone_chain_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:44:50.212964+00:00
-- url     : https://prove2.me/submissions/3abe32b7-68a3-4cd9-a10e-c655046f9527

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
theorem _root_.solution {D A : Finset α} {e v : α}
    (hD_chain : IsChain (D : Set α)) (hA_anti : IsAntichain (A : Set α))
    (heD : e ∈ D) (heA : e ∈ A) (hvD : v ∈ D) (hv_cone : ∃ a ∈ A, a ≤ v) :
    e ≤ v := by
  rcases hD_chain e v heD hvD with hle | hle
  · exact hle
  · rcases hv_cone with ⟨a, ha, ha_le_v⟩
    have : a = e := by by_contra hne; exact (hA_anti a e ha heA hne).1 (ha_le_v.trans hle)
    subst this; exact ha_le_v
end DilworthTheorem

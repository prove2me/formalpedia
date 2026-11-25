-- Prove2me | solution 1 for DilworthTheorem.cover_inter_antichain_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:44:52.569326+00:00
-- url     : https://prove2.me/submissions/76645d37-fea2-4312-ab8b-955266b6739b

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
import Theorems.Thm_DilworthTheorem_chain_inter_antichain_subsingleton

set_option autoImplicit true
open DilworthTheorem
open Finset
open Classical
variable {α : Type*} [PartialOrder α]
namespace DilworthTheorem
theorem _root_.solution {D A : Finset α} {e u : α}
    (hD_chain : IsChain (D : Set α)) (hA_anti : IsAntichain (A : Set α))
    (heD : e ∈ D) (heA : e ∈ A) (huD : u ∈ D) (huA : u ∈ A) : u = e :=
  chain_inter_antichain_subsingleton D A hD_chain hA_anti u e ⟨huD, huA⟩ ⟨heD, heA⟩
end DilworthTheorem

-- Prove2me | solution 1 for C6BipartiteDomination.lemma_7_2_charge_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:52:58.915612+00:00
-- url     : https://prove2.me/submissions/32d0af35-1d0a-471b-84f8-b3fb4eecf320

import Definitions.Def_C6BipartiteDomination_A6
import Definitions.Def_C6BipartiteDomination_A7
import Theorems.Thm_C6BipartiteDomination_lemma_7_2_negative_charge_classification

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {w : V} (hw : w ∈ SPart G D)
    (ha : externalCharge G D w < 0) :
    (kCharge G D w = 3 ∧ betaCharge G D w = 2 ∧ externalCharge G D w = -7) ∨
    (kCharge G D w = 3 ∧ betaCharge G D w = 3 ∧ externalCharge G D w = -4) ∨
    (kCharge G D w = 4 ∧ betaCharge G D w = 2 ∧ externalCharge G D w = -14) := by
  rcases lemma_7_2_negative_charge_classification G hCan hmax hw ha with h | h | h
  · left
    rcases h with ⟨hk, hβ⟩
    simp [externalCharge, hk, hβ]
  · right; left
    rcases h with ⟨hk, hβ⟩
    simp [externalCharge, hk, hβ]
  · right; right
    rcases h with ⟨hk, hβ⟩
    simp [externalCharge, hk, hβ]
end C6BipartiteDomination

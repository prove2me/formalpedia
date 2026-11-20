-- Prove2me | solution 1 for DeletionCode.FiniteConnectedGrowth.connected_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:44.983818+00:00
-- url     : https://prove2.me/submissions/e3d06c1b-9b2d-4820-9f57-7b20e22287c0

import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_FiniteConnectedGrowth
import Theorems.Thm_DeletionCode_FiniteConnectedGrowth_connected_induction

set_option autoImplicit true
open DeletionCode DeletionCode.FiniteConnectedGrowth
variable {α : Type*} [DecidableEq α]
namespace DeletionCode.FiniteConnectedGrowth
theorem _root_.solution (B : Finset α) (r : α → α → Prop)
    (hB : B.Nonempty)
    (hconnected : ∀ a ∈ B, ∀ b ∈ B, Relation.EqvGen (Induced B r) a b)
    (f : Finset α → ℕ) (d : ℕ) (hd : 1 ≤ d)
    (hsingleton : ∀ a ∈ B, f {a} ≤ d)
    (hgrowth : ∀ U : Finset α, U ⊆ B → ∀ w ∈ B, w ∉ U →
      (∃ u ∈ U, r w u ∨ r u w) → f (insert w U) + 1 ≤ f U + d) :
    f B ≤ (d - 1) * B.card + 1 := by
  apply connected_induction B r hB hconnected (fun U => f U ≤ (d - 1) * U.card + 1)
  · intro a ha
    have hbase := hsingleton a ha
    simp only [Finset.card_singleton, Nat.mul_one]
    omega
  · intro U hsub w hwB hwU hadj hbound
    have hstep := hgrowth U hsub w hwB hwU hadj
    rw [Finset.card_insert_of_notMem hwU, Nat.mul_add, Nat.mul_one]
    omega
end DeletionCode.FiniteConnectedGrowth

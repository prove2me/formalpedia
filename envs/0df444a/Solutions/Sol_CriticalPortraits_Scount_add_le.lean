-- Prove2me | solution 1 for CriticalPortraits.Scount_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:39.393584+00:00
-- url     : https://prove2.me/submissions/f7997fc0-1c93-408b-aa6a-8b4de30c3dc1

module
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_Surjectivity

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (U : Finset (ZMod (d * m))) {x y z : ℕ}
    (hxy : x ≤ y) (hyz : y ≤ z) :
    Scount U x y + Scount U y z ≤ Scount U x z := by
  classical
  unfold Scount
  rw [← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    intro t ht
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at ht
    rw [Finset.mem_filter]
    rcases ht with ⟨htU, h1, h2⟩ | ⟨htU, h1, h2⟩
    · exact ⟨htU, h1, lt_of_lt_of_le h2 hyz⟩
    · exact ⟨htU, lt_of_le_of_lt hxy h1, h2⟩
  · rw [Finset.disjoint_left]
    intro t ht1 ht2
    rw [Finset.mem_filter] at ht1 ht2
    omega
end CriticalPortraits

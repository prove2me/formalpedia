-- Prove2me | solution 1 for CriticalPortraits.Scount_antitone_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:36.82449+00:00
-- url     : https://prove2.me/submissions/b0eea7c1-9bad-499b-bd24-bb84557da935

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
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (U : Finset (ZMod (d * m))) {x x' y : ℕ}
    (hxx : x ≤ x') : Scount U x' y ≤ Scount U x y := by
  unfold Scount
  apply Finset.card_le_card
  intro t ht
  rw [Finset.mem_filter] at ht ⊢
  exact ⟨ht.1, lt_of_le_of_lt hxx ht.2.1, ht.2.2⟩
end CriticalPortraits

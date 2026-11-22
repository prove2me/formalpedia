-- Prove2me | solution 1 for CriticalPortraits.Scount_mono_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:32:14.055762+00:00
-- url     : https://prove2.me/submissions/972a70e2-abff-41c7-a181-f662e1b4e387

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
theorem _root_.solution {d m : ℕ} (U : Finset (ZMod (d * m))) {x y y' : ℕ}
    (hyy : y ≤ y') : Scount U x y ≤ Scount U x y' := by
  unfold Scount
  apply Finset.card_le_card
  intro t ht
  rw [Finset.mem_filter] at ht ⊢
  exact ⟨ht.1, ht.2.1, lt_of_lt_of_le ht.2.2 hyy⟩
end CriticalPortraits

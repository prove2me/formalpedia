-- Prove2me | solution 1 for CriticalPortraits.Defc_bot_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:32:03.798043+00:00
-- url     : https://prove2.me/submissions/16b69001-5ef8-4cdd-9324-f90813ac0b31

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
public import Theorems.Thm_CriticalPortraits_Scount_bot_le

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U)
    {u : ZMod (d * m)} (hu : u ∈ U) (hlu : 1 ≤ u.val / m) :
    Defc U (u.val % m) (u.val / m) u.val 0 ≤ 0 := by
  have hScount := Scount_bot_le hd hm hcanon hu
  unfold Defc
  simp only [Nat.zero_mul, Nat.add_zero]
  push_cast
  omega
end CriticalPortraits

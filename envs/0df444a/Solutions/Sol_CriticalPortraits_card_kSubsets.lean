-- Prove2me | solution 1 for CriticalPortraits.card_kSubsets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:24:47.243487+00:00
-- url     : https://prove2.me/submissions/6ec9bfb0-42a4-4ab3-9ecf-5845f1d315fd

module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Core

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
namespace CriticalPortraits
theorem _root_.solution (N k : ℕ) [NeZero N] :
    Fintype.card {S : Finset (ZMod N) // S.card = k} = N.choose k := by
  rw [Fintype.card_finset_len, ZMod.card]
end CriticalPortraits

-- Prove2me | solution 1 for CriticalPortraits.Defc_top_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:09.925644+00:00
-- url     : https://prove2.me/submissions/020ff8cb-1946-4385-9169-dc9b7d65719d

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
theorem _root_.solution {d m : ℕ} (U : Finset (ZMod (d * m))) (φ lu uval : ℕ) (hlu : 1 ≤ lu) :
    0 ≤ Defc U φ lu uval (lu - 1) := by
  unfold Defc
  simp_all
end CriticalPortraits

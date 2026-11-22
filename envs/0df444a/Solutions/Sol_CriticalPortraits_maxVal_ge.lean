-- Prove2me | solution 1 for CriticalPortraits.maxVal_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:27:03.846931+00:00
-- url     : https://prove2.me/submissions/8ccf270a-f43d-439e-b98d-8fc7ef292d41

module
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity

set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {N : ℕ} (S : Finset (ZMod N)) (h : S.Nonempty) :
    ∀ x ∈ S, x.val ≤ (maxVal S h).val :=
  (Finset.exists_max_image S (fun x => x.val) h).choose_spec.2
end CriticalPortraits

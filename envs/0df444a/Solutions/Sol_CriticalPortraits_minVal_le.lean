-- Prove2me | solution 1 for CriticalPortraits.minVal_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:24:43.970856+00:00
-- url     : https://prove2.me/submissions/673db050-d17f-4bc4-8ded-a0f9429dd5cd

module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Portraits

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
namespace CriticalPortraits
theorem _root_.solution {N : ℕ} (S : Finset (ZMod N)) (h : S.Nonempty) :
    ∀ x ∈ S, (minVal S h).val ≤ x.val :=
  (Finset.exists_min_image S (fun x => x.val) h).choose_spec.2
end CriticalPortraits

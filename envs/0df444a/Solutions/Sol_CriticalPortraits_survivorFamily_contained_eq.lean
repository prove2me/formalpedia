-- Prove2me | solution 1 for CriticalPortraits.survivorFamily_contained_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:47.351855+00:00
-- url     : https://prove2.me/submissions/703d155d-036d-41c0-b829-82a4d0462ab7

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
public import Theorems.Thm_CriticalPortraits_hiV_lt_d

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
theorem _root_.solution [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P) :
    AbstractLaminar.contained (survivorFamily hd hm hP) 0 (d - 1) = T P := by
  unfold AbstractLaminar.contained
  apply Finset.filter_true_of_mem
  intro e he
  refine ⟨Nat.zero_le _, ?_⟩
  -- hi e = hiV e ≤ d - 1
  change hiV e ≤ d - 1
  have := hiV_lt_d (d := d) (m := m) hm e
  omega
end CriticalPortraits

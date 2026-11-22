-- Prove2me | solution 1 for CriticalPortraits.survivorFamily_saturated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:29:27.415125+00:00
-- url     : https://prove2.me/submissions/678ab5d9-aac6-4710-88e2-50012a46de7a

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
public import Theorems.Thm_CriticalPortraits_survivorFamily_contained_eq

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
    AbstractLaminar.N (survivorFamily hd hm hP) 0 (d - 1) = (d - 1) - 0 := by
  unfold AbstractLaminar.N
  rw [survivorFamily_contained_eq hd hm hP, T_card hP]
  omega
end CriticalPortraits

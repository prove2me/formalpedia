-- Prove2me | solution 1 for CriticalPortraits.T_injOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:40:33.24187+00:00
-- url     : https://prove2.me/submissions/710d0fa2-ac3b-4d5e-8d1e-1ca5d0b1576f

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
public import Theorems.Thm_CriticalPortraits_T_inj

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
theorem _root_.solution (hd : 0 < d) (hm : 0 < m) :
    Set.InjOn (T (N := d*m)) {P | Portrait d m P} :=
  fun _P₁ h₁ _P₂ h₂ hT => T_inj hd hm h₁ h₂ hT
end CriticalPortraits

-- Prove2me | solution 1 for CriticalPortraits.reach_forced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:38:41.987104+00:00
-- url     : https://prove2.me/submissions/efff1e08-29ae-4b31-8df8-537462fb4e80

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
public import Theorems.Thm_CriticalPortraits_edgeStep_forced

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
    {P₁ P₂ : Finset (Finset (ZMod (d * m)))} (h₁ : Portrait d m P₁) (h₂ : Portrait d m P₂)
    (hT : T P₁ = T P₂) {u v : ZMod (d * m)}
    (hreach : Relation.ReflTransGen (edgeStep P₁) u v) :
    Relation.ReflTransGen (edgeStep P₂) u v := by
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih => exact Relation.ReflTransGen.tail ih (edgeStep_forced hd hm h₁ h₂ hT hbc)
end CriticalPortraits

-- Prove2me | solution 1 for CriticalPortraits.reach_to_low
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:29:19.380575+00:00
-- url     : https://prove2.me/submissions/5ef6e05f-4632-4443-9bcb-fc55733fb868

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
public import Theorems.Thm_CriticalPortraits_hostSet_predIn

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
theorem _root_.solution [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P) :
    ∀ n : ℕ, ∀ z : ZMod (d*m), z.val = n → (hz : z ∈ T P) →
      ∃ q, ∃ hq : q ∈ T P, predIn P q hq ∉ T P ∧
        hostSet P q hq = hostSet P z hz ∧ Relation.ReflTransGen (edgeStep P) z q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z hzn hz
    set p := predIn P z hz with hpdef
    by_cases hpT : p ∈ T P
    · have hpval : p.val < z.val := predIn_val_lt hz
      obtain ⟨q, hq, hqpred, hqhost, hqreach⟩ := ih p.val (by omega) p rfl hpT
      exact ⟨q, hq, hqpred, by rw [hqhost, hostSet_predIn hP hz hpT],
        Relation.ReflTransGen.head ⟨hz, hpT, Or.inl rfl⟩ hqreach⟩
    · exact ⟨z, hz, hpT, rfl, Relation.ReflTransGen.refl⟩
end CriticalPortraits

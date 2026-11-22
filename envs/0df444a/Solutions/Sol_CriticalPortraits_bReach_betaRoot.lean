-- Prove2me | solution 1 for CriticalPortraits.bReach_betaRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:54.085971+00:00
-- url     : https://prove2.me/submissions/cd6ecd25-e40b-4a98-bc28-b59b2c07c9ee

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
public import Theorems.Thm_CriticalPortraits_bReach_trans
public import Theorems.Thm_CriticalPortraits_betaRoot_of_not_mem
public import Theorems.Thm_CriticalPortraits_betaRoot_of_mem

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) (x : ZMod (d * m)) :
    bReach U x (betaRoot hd hm hcanon x) := by
  induction hn : x.val using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    subst hn
    by_cases hx : x ∈ U
    · rw [betaRoot_of_mem hd hm hcanon hx]
      have hlu := survivor_level_pos hd hcanon hx
      have hstep : bAdj U x (betaParent U x) :=
        Or.inr ⟨hx, hlu, rfl⟩
      have hlt : (betaParent U x).val < x.val := betaParent_val_lt hd hm hlu
      have hrec := ih (betaParent U x).val hlt (betaParent U x) rfl
      exact bReach_trans (Relation.ReflTransGen.single hstep) hrec
    · rw [betaRoot_of_not_mem hd hm hcanon hx]; exact bReach_refl x
end CriticalPortraits

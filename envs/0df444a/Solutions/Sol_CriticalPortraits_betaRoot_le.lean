-- Prove2me | solution 1 for CriticalPortraits.betaRoot_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:47.548878+00:00
-- url     : https://prove2.me/submissions/3a9b0aee-cd48-415f-ae1b-a933b570d455

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
    (betaRoot hd hm hcanon x).val ≤ x.val := by
  induction hn : x.val using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    subst hn
    by_cases hx : x ∈ U
    · rw [betaRoot_of_mem hd hm hcanon hx]
      have hlt : (betaParent U x).val < x.val :=
        betaParent_val_lt hd hm (survivor_level_pos hd hcanon hx)
      exact le_trans (ih (betaParent U x).val hlt (betaParent U x) rfl) (le_of_lt hlt)
    · rw [betaRoot_of_not_mem hd hm hcanon hx]
end CriticalPortraits

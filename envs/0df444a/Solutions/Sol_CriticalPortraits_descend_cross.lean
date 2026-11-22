-- Prove2me | solution 1 for CriticalPortraits.descend_cross
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:42.546019+00:00
-- url     : https://prove2.me/submissions/a80a1e4d-92c0-4428-a128-09f9239c9ac7

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
public import Theorems.Thm_CriticalPortraits_betaParent_mem_bVerts

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) (L : ℕ) :
    ∀ w : ZMod (d*m), (betaRoot hd hm hcanon w).val ≤ L → L < w.val →
      ∃ b : ZMod (d*m), b ∈ U ∧ bReach U w b ∧ (betaParent U b).val ≤ L ∧ L < b.val := by
  intro w
  induction hn : w.val using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    subst hn
    intro hroot hLw
    by_cases hwU : w ∈ U
    · -- w is a survivor; either its parent already ≤ L (done with b=w) or recurse
      have hlu := survivor_level_pos hd hcanon hwU
      have hpw_lt : (betaParent U w).val < w.val := betaParent_val_lt hd hm hlu
      by_cases hpL : (betaParent U w).val ≤ L
      · exact ⟨w, hwU, bReach_refl w, hpL, hLw⟩
      · push Not at hpL  -- L < (betaParent U w).val
        have hpwv : betaParent U w ∈ bVerts U := betaParent_mem_bVerts hwU
        have hrooteq : betaRoot hd hm hcanon (betaParent U w) = betaRoot hd hm hcanon w :=
          (betaRoot_of_mem hd hm hcanon hwU).symm
        have hroot' : (betaRoot hd hm hcanon (betaParent U w)).val ≤ L := by
          rw [hrooteq]; exact hroot
        obtain ⟨b, hbU, hbreach, hb1, hb2⟩ :=
          ih (betaParent U w).val hpw_lt (betaParent U w) rfl hroot' hpL
        refine ⟨b, hbU, ?_, hb1, hb2⟩
        exact bReach_trans (Relation.ReflTransGen.single (Or.inr ⟨hwU, hlu, rfl⟩)) hbreach
    · -- w ∉ U ⟹ betaRoot w = w ⟹ w.val ≤ L, contradicting L < w.val
      rw [betaRoot_of_not_mem hd hm hcanon hwU] at hroot
      omega
end CriticalPortraits

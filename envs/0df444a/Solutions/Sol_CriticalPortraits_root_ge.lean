-- Prove2me | solution 1 for CriticalPortraits.root_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:36:26.157972+00:00
-- url     : https://prove2.me/submissions/47a8dbfc-4888-4518-ab3f-138d38bd89fe

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
public import Theorems.Thm_CriticalPortraits_betaParent_inj
public import Theorems.Thm_CriticalPortraits_betaRoot_of_not_mem
public import Theorems.Thm_CriticalPortraits_betaRoot_of_mem
public import Theorems.Thm_CriticalPortraits_betaParent_mem_bVerts
public import Theorems.Thm_CriticalPortraits_noEscape

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U)
    {u : ZMod (d * m)} (hu : u ∈ U) :
    ∀ w : ZMod (d*m), w ∈ bVerts U →
      (betaParent U u).val < w.val → w.val < u.val →
      (betaParent U u).val ≤ (betaRoot hd hm hcanon w).val := by
  have : NeZero (d*m) := ⟨by positivity⟩
  intro w
  induction hn : w.val using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    subst hn
    intro hwv h1 h2
    by_cases hwU : w ∈ U
    · -- survivor: noEscape ⟹ betaParent w ≥ v, and inj ⟹ strict ⟹ recurse
      have hesc := noEscape hd hm hcanon hu hwU h1 h2
      -- betaParent w ≠ betaParent u (else w = u, but w.val < u.val)
      have hne : (betaParent U w).val ≠ (betaParent U u).val := by
        intro heqv
        have heq : betaParent U w = betaParent U u := ZMod.val_injective _ heqv
        have := betaParent_inj hd hm hcanon hwU hu heq
        rw [this] at h2; omega
      have hstrict : (betaParent U u).val < (betaParent U w).val :=
        lt_of_le_of_ne hesc (Ne.symm hne)
      have hpw_lt : (betaParent U w).val < w.val :=
        betaParent_val_lt hd hm (survivor_level_pos hd hcanon hwU)
      have hpw_ltu : (betaParent U w).val < u.val := lt_trans hpw_lt h2
      have hpwv : betaParent U w ∈ bVerts U := betaParent_mem_bVerts hwU
      have hrec := ih (betaParent U w).val hpw_lt (betaParent U w) rfl hpwv hstrict hpw_ltu
      rw [betaRoot_of_mem hd hm hcanon hwU]
      exact hrec
    · -- non-survivor: root is itself
      rw [betaRoot_of_not_mem hd hm hcanon hwU]
      exact le_of_lt h1
end CriticalPortraits

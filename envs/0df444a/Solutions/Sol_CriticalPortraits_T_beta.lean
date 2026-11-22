-- Prove2me | solution 1 for CriticalPortraits.T_beta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:34:51.309123+00:00
-- url     : https://prove2.me/submissions/058cfd74-0253-49e6-b0ee-fceff977cb73

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
public import Theorems.Thm_CriticalPortraits_betaRoot_not_mem
public import Theorems.Thm_CriticalPortraits_mem_bVerts_of_mem
public import Theorems.Thm_CriticalPortraits_minVal_betaBlock
public import Theorems.Thm_CriticalPortraits_mem_U_of_mem_block_ne_root
public import Theorems.Thm_CriticalPortraits_betaBlock_mem_beta
public import Theorems.Thm_CriticalPortraits_mem_beta_iff
public import Theorems.Thm_CriticalPortraits_mem_T
public import Theorems.Thm_CriticalPortraits_mem_eraseMin


set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (hd : 0 < d) (hm : 0 < m) {U : Finset (ZMod (d * m))}
    (hcanon : LevelCanonical d m U) : T (beta U) = U := by
  have : NeZero (d*m) := ⟨by positivity⟩
  ext x
  rw [mem_T]
  constructor
  · -- x ∈ eraseMin S, S = betaBlock U v ⇒ x ∈ U
    rintro ⟨S, hS, hxS⟩
    rw [mem_beta_iff] at hS
    obtain ⟨v, hv, hSeq⟩ := hS
    subst hSeq
    have hne : (betaBlock U v).Nonempty := betaBlock_nonempty hv
    rw [mem_eraseMin (betaBlock U v) hne] at hxS
    obtain ⟨hxmem, hxneq⟩ := hxS
    -- minVal = betaRoot v
    rw [minVal_betaBlock hd hm hcanon hv] at hxneq
    exact mem_U_of_mem_block_ne_root hd hm hcanon hxmem hxneq
  · -- x ∈ U ⇒ x ∈ eraseMin (betaBlock U x)
    intro hxU
    have hxv : x ∈ bVerts U := mem_bVerts_of_mem hxU
    refine ⟨betaBlock U x, betaBlock_mem_beta hxv, ?_⟩
    have hne : (betaBlock U x).Nonempty := betaBlock_nonempty hxv
    rw [mem_eraseMin (betaBlock U x) hne]
    constructor
    · rw [mem_betaBlock]; exact ⟨hxv, bReach_refl x⟩
    · rw [minVal_betaBlock hd hm hcanon hxv]
      -- x ∈ U but betaRoot x ∉ U
      intro hcontra
      have hroot_notmem : betaRoot hd hm hcanon x ∉ U := betaRoot_not_mem hd hm hcanon x
      rw [← hcontra] at hroot_notmem
      exact hroot_notmem hxU
end CriticalPortraits

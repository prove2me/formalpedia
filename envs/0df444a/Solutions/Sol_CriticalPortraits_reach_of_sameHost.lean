-- Prove2me | solution 1 for CriticalPortraits.reach_of_sameHost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:26.144185+00:00
-- url     : https://prove2.me/submissions/752c23cc-4606-429b-b081-ae2f5cd00f2d

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
public import Theorems.Thm_CriticalPortraits_minVal_congr
public import Theorems.Thm_CriticalPortraits_reach_symm
public import Theorems.Thm_CriticalPortraits_reach_to_low
public import Theorems.Thm_CriticalPortraits_mem_T
public import Theorems.Thm_CriticalPortraits_mem_eraseMin


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
theorem _root_.solution [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {x z : ZMod (d * m)} (hx : x ∈ T P) (hz : z ∈ T P)
    (hhost : hostSet P z hz = hostSet P x hx) :
    Relation.ReflTransGen (edgeStep P) z x := by
  obtain ⟨qz, hqz, hqzpred, hqzhost, hqzreach⟩ := reach_to_low hP z.val z rfl hz
  obtain ⟨qx, hqx, hqxpred, hqxhost, hqxreach⟩ := reach_to_low hP x.val x rfl hx
  have hsamehost : hostSet P qz hqz = hostSet P qx hqx := by rw [hqzhost, hqxhost, hhost]
  have hzne : (hostSet P qz hqz).Nonempty := ⟨qz, mem_hostSet hqz⟩
  have hxne : (hostSet P qx hqx).Nonempty := ⟨qx, mem_hostSet hqx⟩
  have hpqz_min : predIn P qz hqz = minVal (hostSet P qz hqz) hzne := by
    by_contra hne
    exact hqzpred (mem_T.mpr ⟨_, hostSet_mem hqz,
      (mem_eraseMin _ hzne _).mpr ⟨predIn_mem_host hqz, hne⟩⟩)
  have hpqx_min : predIn P qx hqx = minVal (hostSet P qx hqx) hxne := by
    by_contra hne
    exact hqxpred (mem_T.mpr ⟨_, hostSet_mem hqx,
      (mem_eraseMin _ hxne _).mpr ⟨predIn_mem_host hqx, hne⟩⟩)
  have hpredeq : predIn P qz hqz = predIn P qx hqx := by
    rw [hpqz_min, hpqx_min]; exact minVal_congr hzne hxne hsamehost
  have hqeq : qz = qx := by
    by_contra hqne
    have hqzlt : (predIn P qz hqz).val < qz.val := predIn_val_lt hqz
    have hqxlt : (predIn P qx hqx).val < qx.val := predIn_val_lt hqx
    have hqxinz : qx ∈ hostSet P qz hqz := by rw [hsamehost]; exact mem_hostSet hqx
    have hqzinx : qz ∈ hostSet P qx hqx := by rw [← hsamehost]; exact mem_hostSet hqz
    rcases lt_trichotomy qz.val qx.val with hlt | heq | hgt
    · exact predIn_immediate hqx hqzinx (by rw [← hpredeq]; exact hqzlt) hlt
    · exact hqne (ZMod.val_injective _ heq)
    · exact predIn_immediate hqz hqxinz (by rw [hpredeq]; exact hqxlt) hgt
  subst hqeq
  exact hqzreach.trans (reach_symm hqxreach)
end CriticalPortraits

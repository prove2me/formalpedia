-- Prove2me | solution 1 for CriticalPortraits.hostSet_forced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:39:16.020967+00:00
-- url     : https://prove2.me/submissions/d96e8c03-5214-4810-b41f-12f64de372e0

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
public import Theorems.Thm_CriticalPortraits_predIn_forced
public import Theorems.Thm_CriticalPortraits_hostSet_eq_of_mem
public import Theorems.Thm_CriticalPortraits_minVal_congr
public import Theorems.Thm_CriticalPortraits_reach_symm
public import Theorems.Thm_CriticalPortraits_reach_sameHost
public import Theorems.Thm_CriticalPortraits_reach_to_low
public import Theorems.Thm_CriticalPortraits_reach_of_sameHost
public import Theorems.Thm_CriticalPortraits_reach_forced
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
theorem _root_.solution [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P₁ P₂ : Finset (Finset (ZMod (d * m)))} (h₁ : Portrait d m P₁) (h₂ : Portrait d m P₂)
    (hT : T P₁ = T P₂) {x : ZMod (d * m)} (hx₁ : x ∈ T P₁) (hx₂ : x ∈ T P₂) :
    hostSet P₁ x hx₁ = hostSet P₂ x hx₂ := by
  -- symmetric subset argument
  suffices H : ∀ (Q₁ Q₂ : Finset (Finset (ZMod (d*m)))), Portrait d m Q₁ → Portrait d m Q₂ →
      T Q₁ = T Q₂ → ∀ (y : ZMod (d*m)) (hy₁ : y ∈ T Q₁) (hy₂ : y ∈ T Q₂),
        hostSet Q₁ y hy₁ ⊆ hostSet Q₂ y hy₂ by
    exact Finset.Subset.antisymm (H P₁ P₂ h₁ h₂ hT x hx₁ hx₂)
      (H P₂ P₁ h₂ h₁ hT.symm x hx₂ hx₁)
  intro Q₁ Q₂ hQ₁ hQ₂ hTQ y hy₁ hy₂ z hz
  by_cases hzT : z ∈ T Q₁
  · -- z survivor of y's block: reachable from y in Q₁; transfer to Q₂.
    have hzhost : hostSet Q₁ z hzT = hostSet Q₁ y hy₁ :=
      hostSet_eq_of_mem hQ₁ hzT (hostSet_mem hy₁) hz
    have hreach₁ : Relation.ReflTransGen (edgeStep Q₁) z y := reach_of_sameHost hQ₁ hy₁ hzT hzhost
    have hzT₂ : z ∈ T Q₂ := hTQ ▸ hzT
    have hzhost₂ : hostSet Q₂ z hzT₂ = hostSet Q₂ y hy₂ :=
      reach_sameHost hQ₂ hy₂ (reach_symm (reach_forced hd hm hQ₁ hQ₂ hTQ hreach₁)) hzT₂
    rw [← hzhost₂]; exact mem_hostSet hzT₂
  · -- z ∉ T Q₁: z is the root (minVal) of y's Q₁-block.
    have hyne₁ : (hostSet Q₁ y hy₁).Nonempty := ⟨y, mem_hostSet hy₁⟩
    have hzmin : z = minVal (hostSet Q₁ y hy₁) hyne₁ := by
      by_contra hne
      exact hzT (mem_T.mpr ⟨_, hostSet_mem hy₁, (mem_eraseMin _ hyne₁ z).mpr ⟨hz, hne⟩⟩)
    obtain ⟨q, hq, hqpred, hqhost, hqreach⟩ := reach_to_low hQ₁ y.val y rfl hy₁
    have hqne : (hostSet Q₁ q hq).Nonempty := ⟨q, mem_hostSet hq⟩
    have hpq_min : predIn Q₁ q hq = minVal (hostSet Q₁ q hq) hqne := by
      by_contra hne
      exact hqpred (mem_T.mpr ⟨_, hostSet_mem hq,
        (mem_eraseMin _ hqne _).mpr ⟨predIn_mem_host hq, hne⟩⟩)
    have hpq_z : predIn Q₁ q hq = z := by
      rw [hpq_min, hzmin]; exact minVal_congr hqne hyne₁ hqhost
    have hq₂ : q ∈ T Q₂ := hTQ ▸ hq
    have hpredeq : predIn Q₁ q hq = predIn Q₂ q hq₂ := predIn_forced hd hm hQ₁ hQ₂ hTQ hq hq₂
    have hpq_z₂ : predIn Q₂ q hq₂ = z := by rw [← hpredeq]; exact hpq_z
    have hqhost₂ : hostSet Q₂ q hq₂ = hostSet Q₂ y hy₂ := by
      have hreach₁ : Relation.ReflTransGen (edgeStep Q₁) q y := reach_of_sameHost hQ₁ hy₁ hq hqhost
      exact reach_sameHost hQ₂ hy₂ (reach_symm (reach_forced hd hm hQ₁ hQ₂ hTQ hreach₁)) hq₂
    rw [← hqhost₂, ← hpq_z₂]; exact predIn_mem_host hq₂
end CriticalPortraits

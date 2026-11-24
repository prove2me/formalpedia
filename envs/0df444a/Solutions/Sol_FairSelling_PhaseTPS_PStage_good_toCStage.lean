-- Prove2me | solution 1 for FairSelling.PhaseTPS.PStage.good_toCStage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:47:53.542299+00:00
-- url     : https://prove2.me/submissions/4eb653ed-2a18-4a69-9772-b7fc3ee35877

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxPhase
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_charge
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_served
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_bundle
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_cash
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_resv
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_bank
import Theorems.Thm_FairSelling_PhaseTPS_PStage_charge_subset
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_soldSet
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_cost
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_bundle
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_cash
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_served
attribute [local simp] FairSelling.restrictVal_mem


attribute [local simp] FairSelling.PhaseTPS.PStage.toCStage_served
attribute [local simp] FairSelling.PhaseTPS.PStage.toCStage_bundle
attribute [local simp] FairSelling.PhaseTPS.PStage.toCStage_cash
attribute [local simp] FairSelling.PhaseTPS.PStage.toCStage_resv
attribute [local simp] FairSelling.PhaseTPS.PStage.toCStage_bank

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PhaseTPS.PStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
namespace FairSelling.PhaseTPS.PStage
theorem _root_.solution {s : PStage G n} (hs : s.Good v p eps) :
    (s.toCStage).Good v p eps := by
  classical
  refine ⟨?_, hs.bundle_disj, ?_, ?_, hs.cash_nonneg, hs.resv_nonneg, hs.bank_nonneg, ?_, ?_,
    ?_, ?_⟩
  · -- unserved agents hold nothing
    intro i hi
    obtain ⟨hb, ho, he, hc, hr⟩ := hs.unserved i hi
    refine ⟨hb, ?_, hc, hr⟩
    rw [toCStage_charge, ho, he]
    simp
  · -- charges are pairwise disjoint
    intro i j hij
    rw [toCStage_charge, toCStage_charge]
    refine Finset.disjoint_union_left.mpr ⟨?_, ?_⟩
    · refine Finset.disjoint_union_right.mpr ⟨hs.own_disj i j hij, ?_⟩
      exact Finset.disjoint_of_subset_right (Finset.filter_subset _ _) (hs.own_ext i j)
    · refine Finset.disjoint_union_right.mpr ⟨?_, ?_⟩
      · exact Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
          (hs.own_ext j i).symm
      · refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
        have h1 := (Finset.mem_filter.mp hx).2
        have h2 := (Finset.mem_filter.mp hx').2
        have hxi : x ∈ s.charge i :=
          Finset.mem_union_right _ (Finset.mem_of_mem_filter _ hx)
        have hxj : x ∈ s.charge j :=
          Finset.mem_union_right _ (Finset.mem_of_mem_filter _ hx')
        exact hij (le_antisymm (h1 j hxj) (h2 i hxi))
  · -- sold goods are in nobody's bundle
    intro i j
    exact Finset.disjoint_of_subset_left (charge_subset s i) (hs.charge_bundle i j)
  · -- the money equation
    show (∑ i, s.cash i) + (∑ i, s.resv i) + s.bank = ∑ g ∈ (s.toCStage).soldSet, p g
    rw [toCStage_soldSet]
    exact hs.money
  · exact hs.share
  · -- safety
    intro i hi j
    rcases hs.safe i hi j with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, h3⟩
  · -- the cost bound
    intro i hi j hj
    rw [toCStage_cost v p eps hs i j hj]
    exact hs.cost_le i hi j hj
end FairSelling.PhaseTPS.PStage

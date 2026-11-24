-- Prove2me | solution 1 for FairSelling.PhaseTPS.PStage.toCStage_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:46:12.371341+00:00
-- url     : https://prove2.me/submissions/dbfac10c-157c-4f0e-b42c-e9029729bbdc

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxPhase
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_charge
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_served
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_bundle
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_cash
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_resv
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_bank
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
theorem _root_.solution {s : PStage G n} (hs : s.Good v p eps) (i j : Fin n) (hj : j ∉ s.served) :
    (s.toCStage).cost v p i j = s.cost v p i j := by
  classical
  have hdisj : Disjoint (s.own i) ((s.ext i).filter (fun g => ∀ k, g ∈ s.charge k → i ≤ k)) :=
    Finset.disjoint_of_subset_right (Finset.filter_subset _ _) (hs.own_ext i i)
  have hsum : ∑ g ∈ (s.ext i).filter (fun g => ∀ k, g ∈ s.charge k → i ≤ k),
      saleLoss (v j) p (TPS n (v j) p) g
      = ∑ g ∈ s.ext i, saleLoss (v j) p (TPS n (v j) p) g := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro x hx hxF
    obtain ⟨k, hk, hik⟩ : ∃ k, x ∈ s.charge k ∧ ¬ (i ≤ k) := by
      by_contra hc
      push_neg at hc
      exact hxF (Finset.mem_filter.mpr ⟨hx, hc⟩)
    have hki : k ≠ i := by rintro rfl; exact hik le_rfl
    have hxk : x ∈ s.ext k := by
      rcases Finset.mem_union.mp hk with h | h
      · exact absurd hx (Finset.disjoint_left.mp (hs.own_ext k i) h)
      · exact h
    exact hs.ext_uniq i k (Ne.symm hki) x hx hxk j hj
  unfold ChargeTPS.CStage.cost PStage.cost
  rw [toCStage_charge, Finset.sum_union hdisj, hsum]
  simp only [toCStage_bundle, toCStage_cash, toCStage_resv]
  ring
end FairSelling.PhaseTPS.PStage

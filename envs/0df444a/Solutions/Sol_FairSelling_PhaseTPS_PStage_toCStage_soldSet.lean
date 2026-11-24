-- Prove2me | solution 1 for FairSelling.PhaseTPS.PStage.toCStage_soldSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:00:35.653732+00:00
-- url     : https://prove2.me/submissions/f4bd22fd-027f-4516-9297-c7415d248417

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
omit [Fintype G]
namespace FairSelling.PhaseTPS.PStage
theorem _root_.solution (s : PStage G n) : (s.toCStage).soldSet = s.sold := by
  classical
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [ChargeTPS.CStage.soldSet, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
    obtain ⟨i, hi⟩ := hx
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, charge_subset s i hi⟩
  · intro x hx
    simp only [PStage.sold, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
    obtain ⟨i, hi⟩ := hx
    -- take the least agent charged with `x`
    set T : Finset (Fin n) := Finset.univ.filter (fun k => x ∈ s.charge k) with hT
    have hTne : T.Nonempty := ⟨i, by simp [hT, hi]⟩
    set i0 := T.min' hTne with hi0
    have hi0mem : x ∈ s.charge i0 := by
      have := T.min'_mem hTne
      simp only [hT, Finset.mem_filter] at this
      exact this.2
    have hmin : ∀ k, x ∈ s.charge k → i0 ≤ k := by
      intro k hk
      exact T.min'_le k (by simp [hT, hk])
    refine Finset.mem_biUnion.mpr ⟨i0, Finset.mem_univ i0, ?_⟩
    rw [toCStage_charge]
    rcases Finset.mem_union.mp hi0mem with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨h, hmin⟩)
end FairSelling.PhaseTPS.PStage

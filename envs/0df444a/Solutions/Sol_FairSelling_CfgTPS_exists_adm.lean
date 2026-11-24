-- Prove2me | solution 1 for FairSelling.CfgTPS.exists_adm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:57:57.436803+00:00
-- url     : https://prove2.me/submissions/c6743ec3-118c-4fa9-969f-d07d42b18853

import Mathlib
import Definitions.Def_RequestProject_TPSSefxCharge
import Definitions.Def_RequestProject_TPSSefxServe
import Definitions.Def_RequestProject_TPSSefxConfig
import Theorems.Thm_FairSelling_CfgTPS_Qc_nonneg
import Theorems.Thm_FairSelling_CfgTPS_Qc_le_of_gap
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_bundle
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_cash
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_served
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.CfgTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (w : Fin n → G → ℝ) (p : G → ℝ) (req : Fin n → ℝ) (k0 : Fin n) (D : ℝ)
omit [Fintype G]
namespace FairSelling.CfgTPS
theorem _root_.solution (hp : ∀ g, 0 ≤ p g) :
    ∀ (c : ℕ) (S S₀ : Finset G), S.card ≤ c → Disjoint S S₀ → Feas w p req k0 D S S₀ →
      ∃ T T₀ : Finset G, T ⊆ S ∧ S₀ ⊆ T₀ ∧ T ∪ T₀ = S ∪ S₀ ∧ Disjoint T T₀ ∧
        Adm w p req k0 D T T₀ := by
  intro c
  induction c with
  | zero =>
    intro S S₀ hcard hdisj hfeas
    have hS : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    subst hS
    refine ⟨∅, S₀, Finset.Subset.refl _, Finset.Subset.refl _, rfl, hdisj, hfeas, ?_⟩
    intro X hX hXne m
    exact absurd (Finset.subset_empty.mp hX ▸ hXne) (by simp)
  | succ c ih =>
    intro S S₀ hcard hdisj hfeas
    by_cases hadm : ∀ X ⊆ S, X.Nonempty → ∀ m,
        vbarSum (w m) p (S \ X) + (∑ g ∈ X, p g) + Qc w p req k0 S ≤ req m
    · exact ⟨S, S₀, Finset.Subset.refl _, Finset.Subset.refl _, rfl, hdisj, hfeas, hadm⟩
    · push_neg at hadm
      obtain ⟨X, hXS, hXne, m, hm⟩ := hadm
      have hXS₀ : Disjoint X S₀ := Finset.disjoint_of_subset_left hXS hdisj
      have hpX : 0 ≤ ∑ g ∈ X, p g := Finset.sum_nonneg (fun g _ => hp g)
      have hfeas' : Feas w p req k0 D (S \ X) (S₀ ∪ X) := by
        have h1 : Qc w p req k0 (S \ X) ≤ (∑ g ∈ X, p g) + Qc w p req k0 S := by
          refine Qc_le_of_gap w p req k0 (by linarith [Qc_nonneg w p req k0 S]) m ?_
          linarith
        have h2 : ∑ g ∈ S₀ ∪ X, p g = (∑ g ∈ S₀, p g) + ∑ g ∈ X, p g :=
          Finset.sum_union hXS₀.symm
        unfold Feas at hfeas ⊢
        rw [h2]
        linarith
      have hcard' : (S \ X).card ≤ c := by
        have : (S \ X).card < S.card := by
          refine Finset.card_lt_card ?_
          refine ⟨Finset.sdiff_subset, ?_⟩
          obtain ⟨x, hx⟩ := hXne
          intro hcon
          have := hcon (hXS hx)
          simp only [Finset.mem_sdiff] at this
          exact this.2 hx
        omega
      have hdisj' : Disjoint (S \ X) (S₀ ∪ X) := by
        refine Finset.disjoint_union_right.mpr ⟨?_, ?_⟩
        · exact Finset.disjoint_of_subset_left Finset.sdiff_subset hdisj
        · exact Finset.sdiff_disjoint
      obtain ⟨T, T₀, hT, hT₀, hTU, hTdisj, hTadm⟩ := ih (S \ X) (S₀ ∪ X) hcard' hdisj' hfeas'
      refine ⟨T, T₀, Finset.Subset.trans hT Finset.sdiff_subset,
        Finset.Subset.trans Finset.subset_union_left hT₀,
        ?_, hTdisj, hTadm⟩
      rw [hTU]
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff]
      by_cases hx : x ∈ X
      · have := hXS hx
        tauto
      · tauto
end FairSelling.CfgTPS

-- Prove2me | solution 1 for FairSelling.CfgTPS.exists_min_adm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:59:37.791524+00:00
-- url     : https://prove2.me/submissions/aec02d6e-beba-4c3b-a78c-0b5c5e1f08f3

import Mathlib
import Definitions.Def_RequestProject_TPSSefxCharge
import Definitions.Def_RequestProject_TPSSefxServe
import Definitions.Def_RequestProject_TPSSefxConfig
import Theorems.Thm_FairSelling_CfgTPS_exists_adm
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
open Classical
namespace FairSelling.CfgTPS
theorem _root_.solution (P : Finset G) (hp : ∀ g, 0 ≤ p g) (hfeasP : Feas w p req k0 D P ∅) :
    ∃ S S₀ : Finset G, S ∪ S₀ ⊆ P ∧ Disjoint S S₀ ∧ Adm w p req k0 D S S₀ ∧
      ∀ T T₀ : Finset G, T ∪ T₀ ⊆ P → Disjoint T T₀ → Adm w p req k0 D T T₀ →
        (S ∪ S₀).card * (P.card + 1) + S₀.card
          ≤ (T ∪ T₀).card * (P.card + 1) + T₀.card := by
  classical
  set C : Finset (Finset G × Finset G) :=
    (P.powerset ×ˢ P.powerset).filter (fun x => Disjoint x.1 x.2 ∧ Adm w p req k0 D x.1 x.2)
    with hC
  have hCne : C.Nonempty := by
    obtain ⟨T, T₀, hT, hT₀, hTU, hTdisj, hTadm⟩ :=
      exists_adm w p req k0 D hp P.card P ∅ le_rfl (by simp) hfeasP
    refine ⟨(T, T₀), ?_⟩
    have hT₀P : T₀ ⊆ P := by
      intro x hx
      have : x ∈ T ∪ T₀ := Finset.mem_union_right _ hx
      rw [hTU] at this
      simpa using this
    simp only [hC, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
    exact ⟨⟨hT, hT₀P⟩, hTdisj, hTadm⟩
  obtain ⟨x, hxC, hxmin⟩ := Finset.exists_min_image C
    (fun x => (x.1 ∪ x.2).card * (P.card + 1) + x.2.card) hCne
  simp only [hC, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hxC
  refine ⟨x.1, x.2, Finset.union_subset hxC.1.1 hxC.1.2, hxC.2.1, hxC.2.2, ?_⟩
  intro T T₀ hTP hTdisj hTadm
  refine hxmin (T, T₀) ?_
  simp only [hC, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
  exact ⟨⟨Finset.Subset.trans Finset.subset_union_left hTP,
    Finset.Subset.trans Finset.subset_union_right hTP⟩, hTdisj, hTadm⟩
end FairSelling.CfgTPS

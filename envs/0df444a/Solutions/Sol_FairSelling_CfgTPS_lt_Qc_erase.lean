-- Prove2me | solution 1 for FairSelling.CfgTPS.lt_Qc_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:44:16.000838+00:00
-- url     : https://prove2.me/submissions/9019ba45-5da4-4491-a71b-b0fe5a7292f1

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
variable {w p req k0 D}
omit [Fintype G]
namespace FairSelling.CfgTPS
theorem _root_.solution {P S S₀ : Finset G} (hp : ∀ g, 0 ≤ p g) (hUP : S ∪ S₀ ⊆ P)
    (hmin : ∀ T T₀ : Finset G, T ∪ T₀ ⊆ P → Disjoint T T₀ → Adm w p req k0 D T T₀ →
        (S ∪ S₀).card * (P.card + 1) + S₀.card ≤ (T ∪ T₀).card * (P.card + 1) + T₀.card)
    {g : G} (hg : g ∈ S ∪ S₀) : D < Qc w p req k0 ((S ∪ S₀) \ {g}) := by
  classical
  by_contra hcon
  push_neg at hcon
  set U := S ∪ S₀ with hU
  have hfeas : Feas w p req k0 D (U \ {g}) ∅ := by
    unfold Feas
    simpa using hcon
  obtain ⟨T, T₀, hT, _, hTU, hTdisj, hTadm⟩ :=
    exists_adm w p req k0 D hp (U \ {g}).card (U \ {g}) ∅ le_rfl (by simp) hfeas
  have hTUeq : T ∪ T₀ = U \ {g} := by rw [hTU]; simp
  have hTP : T ∪ T₀ ⊆ P := by rw [hTUeq]; exact Finset.Subset.trans Finset.sdiff_subset hUP
  have hkey := hmin T T₀ hTP hTdisj hTadm
  rw [hTUeq] at hkey
  have hcardU : (U \ {g}).card = U.card - 1 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hg]
  have hUpos : 1 ≤ U.card := Finset.card_pos.mpr ⟨g, hg⟩
  have hT₀P : T₀ ⊆ P := Finset.Subset.trans (Finset.Subset.trans Finset.subset_union_right
    (le_of_eq hTUeq)) (Finset.Subset.trans Finset.sdiff_subset hUP)
  have hT₀card : T₀.card ≤ P.card := Finset.card_le_card hT₀P
  rw [hcardU] at hkey
  have hUcardP : U.card ≤ P.card := Finset.card_le_card hUP
  nlinarith [hkey, hT₀card, hUpos, Nat.sub_add_cancel hUpos]
end FairSelling.CfgTPS

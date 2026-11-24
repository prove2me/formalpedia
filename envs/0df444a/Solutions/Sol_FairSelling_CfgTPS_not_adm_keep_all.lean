-- Prove2me | solution 1 for FairSelling.CfgTPS.not_adm_keep_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:44:21.367907+00:00
-- url     : https://prove2.me/submissions/af9fba9e-dff6-423b-904d-a0a83d5f356b

import Mathlib
import Definitions.Def_RequestProject_TPSSefxCharge
import Definitions.Def_RequestProject_TPSSefxServe
import Definitions.Def_RequestProject_TPSSefxConfig
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
theorem _root_.solution {P S S₀ : Finset G} (hUP : S ∪ S₀ ⊆ P)
    (hmin : ∀ T T₀ : Finset G, T ∪ T₀ ⊆ P → Disjoint T T₀ → Adm w p req k0 D T T₀ →
        (S ∪ S₀).card * (P.card + 1) + S₀.card ≤ (T ∪ T₀).card * (P.card + 1) + T₀.card)
    (hS₀ : S₀.Nonempty) : ¬ Adm w p req k0 D (S ∪ S₀) ∅ := by
  intro hadm
  have := hmin (S ∪ S₀) ∅ (by simpa using hUP) (by simp) hadm
  simp only [Finset.union_empty, Finset.card_empty, add_zero] at this
  have : S₀.card = 0 := by omega
  exact absurd (Finset.card_eq_zero.mp this) (Finset.nonempty_iff_ne_empty.mp hS₀)
end FairSelling.CfgTPS

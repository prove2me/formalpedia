-- Prove2me | solution 1 for FairSelling.PotTPS.pot_of_update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:51:05.18336+00:00
-- url     : https://prove2.me/submissions/6e5f074d-d81b-43b4-8ad9-78ac7473a668

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPot
import Definitions.Def_RequestProject_TPSSefxPotStep
import Theorems.Thm_FairSelling_PotTPS_sum_of_update
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_bundle
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_cash
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_served
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_soldSet
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_bundle
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_cash
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_served
attribute [local simp] FairSelling.PotTPS.QStage.toStage_bundle
attribute [local simp] FairSelling.PotTPS.QStage.toStage_cash
attribute [local simp] FairSelling.PotTPS.QStage.toStage_served
attribute [local simp] FairSelling.PotTPS.QStage.toStage_soldSet
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G]
namespace FairSelling.PotTPS
theorem _root_.solution {s t : QStage G n} {k : Fin n} {Src : Finset G} {q : ℝ} (p : G → ℝ)
    (hsrc : t.src = Function.update s.src k Src) (hcash : t.cash = Function.update s.cash k q)
    (g : G) :
    t.pot p g = s.pot p g + (if g ∈ s.src k then s.cash k else 0)
      - (if g ∈ Src then q else 0) := by
  classical
  have key : ∀ u : QStage G n, ∑ i ∈ u.holders g, u.cash i
      = ∑ i, (if g ∈ u.src i then u.cash i else 0) := by
    intro u; rw [QStage.holders, Finset.sum_filter]
  have hne : ∀ i, i ≠ k → (if g ∈ t.src i then t.cash i else 0)
      = (if g ∈ s.src i then s.cash i else 0) := by
    intro i hi; simp [hsrc, hcash, Function.update_of_ne hi]
  have ht : ∑ i, (if g ∈ t.src i then t.cash i else 0)
      = ∑ i, (if g ∈ s.src i then s.cash i else 0) - (if g ∈ s.src k then s.cash k else 0)
        + (if g ∈ t.src k then t.cash k else 0) :=
    sum_of_update (fun i => if g ∈ s.src i then s.cash i else 0)
      (fun i => if g ∈ t.src i then t.cash i else 0) k hne
  have h1 : (if g ∈ t.src k then t.cash k else 0) = (if g ∈ Src then q else 0) := by
    simp [hsrc, hcash]
  have e1 : t.pot p g = p g - ∑ i, (if g ∈ t.src i then t.cash i else 0) := by
    rw [show t.pot p g = p g - ∑ i ∈ t.holders g, t.cash i from rfl, key t]
  have e2 : s.pot p g = p g - ∑ i, (if g ∈ s.src i then s.cash i else 0) := by
    rw [show s.pot p g = p g - ∑ i ∈ s.holders g, s.cash i from rfl, key s]
  rw [e1, e2, ht, h1]
  ring
end FairSelling.PotTPS

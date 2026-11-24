-- Prove2me | solution 1 for FairSelling.PotTPS.QStage.cost_le_of_src
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:45:33.720124+00:00
-- url     : https://prove2.me/submissions/ac5ad790-fc38-49ce-909f-8b17f2e5fab8

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
import Theorems.Thm_FairSelling_PotTPS_slice_cost_le
import Theorems.Thm_FairSelling_PotTPS_QStage_cash_add_pot_le
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_ChargeTPS_TPS_le_two_thr
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_bundle
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_cash
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_served
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PotTPS.QStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
variable {v p eps}
namespace FairSelling.PotTPS.QStage
theorem _root_.solution (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) {s : QStage G n} (hs : s.Good v p eps)
    {i : Fin n} (hi : s.src i ≠ ∅) {j : Fin n}
    (hcash : s.cash i ≤ GeneralTPS.thr v p j) :
    s.cost v p i j ≤ 2 * GeneralTPS.thr v p j := by
  obtain ⟨hb, ho, hr⟩ := hs.cutter i hi
  obtain ⟨g, hg⟩ : ∃ g, s.src i = {g} := by
    have h1 := hs.src_card i
    have h2 : (s.src i).card ≠ 0 := fun h => hi (Finset.card_eq_zero.mp h)
    exact Finset.card_eq_one.mp (by omega)
  have hgs : g ∈ s.src i := by rw [hg]; simp
  have hle := cash_add_pot_le hs hgs
  have ht := ChargeTPS.TPS_le_two_thr v p hn hp j
  have := slice_cost_le (v j) p (TPS n (v j) p) (GeneralTPS.thr v p j) g (s.cash i)
    (s.pot p g) hle hcash ht
  simp only [cost, hb, ho, hr, hg, truncBundle, Finset.sum_empty, Finset.sum_singleton,
    zero_add, add_zero]
  linarith
end FairSelling.PotTPS.QStage

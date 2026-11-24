-- Prove2me | solution 1 for FairSelling.PhaseTPS.exists_TPS_SEFX_of_Pstep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:44:55.921272+00:00
-- url     : https://prove2.me/submissions/a1d8a179-b7f1-41a0-80f4-1e95e017bbe7

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxPhase
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_served
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_bundle
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_cash
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_resv
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_bank
import Theorems.Thm_FairSelling_PhaseTPS_PStage_good_toCStage
import Theorems.Thm_FairSelling_PhaseTPS_good_emptyPStage
import Theorems.Thm_FairSelling_PhaseTPS_pdescent
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_ChargeTPS_exists_TPS_SEFX_of_Cstep
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
namespace FairSelling.PhaseTPS
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hp : ∀ g, 0 ≤ p g) (hstep : ∀ eps : ℝ, 0 < eps → PImprovementStep v p eps) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o := by
  classical
  refine ChargeTPS.exists_TPS_SEFX_of_Cstep v p hn hp ?_
  intro eps heps s hs hfull
  -- the charged improvement step is only ever applied to stages coming from `PStage`s, so we
  -- run the descent at the level of `PStage` and re-package the outcome
  obtain ⟨s0, hs0, hs0full⟩ := pdescent v p eps hn hp heps (hstep eps heps) n
    (emptyPStage G n) (good_emptyPStage v p eps) (by simp [emptyPStage])
  refine ⟨s0.toCStage, PStage.good_toCStage v p eps hs0, ?_⟩
  left
  have h1 : s.served.card < n := by
    have h2 : s.served ⊂ Finset.univ := ⟨Finset.subset_univ _, fun h => hfull
      (Finset.Subset.antisymm (Finset.subset_univ _) h)⟩
    have := Finset.card_lt_card h2
    simpa using this
  have h3 : (s0.toCStage).served.card = n := by
    show s0.served.card = n
    rw [hs0full]; simp
  omega
end FairSelling.PhaseTPS

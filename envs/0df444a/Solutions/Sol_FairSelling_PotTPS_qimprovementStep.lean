-- Prove2me | solution 1 for FairSelling.PotTPS.qimprovementStep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:01:37.016804+00:00
-- url     : https://prove2.me/submissions/0658f7d8-43c5-4a4e-9d58-666beacae34e

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPotStep
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPotImp
import Theorems.Thm_FairSelling_PotTPS_qfeas_pool
import Theorems.Thm_FairSelling_PotTPS_qcut_step
import Theorems.Thm_FairSelling_PotTPS_qsell_step
import Theorems.Thm_FairSelling_PotTPS_qbagfill_step
import Theorems.Thm_FairSelling_CfgTPS_Qc_empty_le
import Theorems.Thm_FairSelling_ChargeTPS_req_eq_thr
import Theorems.Thm_FairSelling_ChargeTPS_req_nonneg
import Theorems.Thm_FairSelling_GeneralTPS_thr_nonneg
import Theorems.Thm_FairSelling_PotTPS_QStage_req_eq_thr
import Theorems.Thm_FairSelling_PotTPS_QStage_req_nonneg


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
namespace FairSelling.PotTPS
theorem _root_.solution (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps) :
    QImprovementStep v p eps := by
  classical
  intro s hs hfull
  obtain ⟨k0, hk0⟩ : ∃ k0, k0 ∉ s.served := by
    by_contra hcon
    push_neg at hcon
    exact hfull (Finset.eq_univ_of_forall hcon)
  have hreq0 : ∀ m, 0 ≤ s.req v p eps m := fun m => QStage.req_nonneg hn hp heps hs m
  have hqreq : ∀ m, CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) ≤ s.req v p eps m := fun m =>
    CfgTPS.Qc_empty_le (w := v) (p := p) (k0 := k0) hreq0 m
  by_cases hbig : ∃ g ∈ s.pool, ∃ j, j ∉ s.served ∧ 2 * GeneralTPS.thr v p j < p g
  · obtain ⟨g, hg, j0, hj0, hbg⟩ := hbig
    have h1 : CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) ≤ GeneralTPS.thr v p j0 := by
      have := hqreq j0
      rwa [QStage.req_eq_thr hj0] at this
    have h2 : 0 ≤ GeneralTPS.thr v p j0 := GeneralTPS.thr_nonneg v p hn hp j0
    exact qsell_step v p eps hn hp heps hs k0 hg (by linarith)
  · push_neg at hbig
    by_cases hA : ∃ g0 ∈ s.cutSet, CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) ≤ s.pot p g0
    · obtain ⟨g0, hg0, hle⟩ := hA
      exact qcut_step v p eps hn hp heps hs k0 hg0 hle
    · push_neg at hA
      have hsmall : ∀ g ∈ s.cutSet, s.pot p g ≤ GeneralTPS.thr v p k0 := by
        intro g hg
        have h1 := hA g hg
        have h2 := hqreq k0
        rw [QStage.req_eq_thr hk0] at h2
        linarith
      exact qbagfill_step v p eps hn hp heps hs (qfeas_pool v p eps hn hp hs hk0 hsmall) hbig
end FairSelling.PotTPS

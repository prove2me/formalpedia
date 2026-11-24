-- Prove2me | solution 1 for FairSelling.PhaseTPS.pimprovementStep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:44:58.672802+00:00
-- url     : https://prove2.me/submissions/29ee86b1-e0cc-425b-a72c-339f03ed2f2e

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhaseStep
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPhaseImp
import Theorems.Thm_FairSelling_PhaseTPS_preq_nonneg
import Theorems.Thm_FairSelling_PhaseTPS_preq_eq_thr
import Theorems.Thm_FairSelling_PhaseTPS_pfeas_pool
import Theorems.Thm_FairSelling_PhaseTPS_pbagfill_step
import Theorems.Thm_FairSelling_PhaseTPS_pshare_step
import Theorems.Thm_FairSelling_CfgTPS_Qc_empty_le
import Theorems.Thm_FairSelling_GeneralTPS_thr_nonneg


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
namespace FairSelling.PhaseTPS
theorem _root_.solution (hcarrier : PCarrierReassign v p eps)
    (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps) :
    PImprovementStep v p eps := by
  classical
  intro s hs hfull
  obtain ⟨k0, hk0⟩ : ∃ k0, k0 ∉ s.served := by
    by_contra hcon
    push_neg at hcon
    exact hfull (Finset.eq_univ_of_forall hcon)
  by_cases hB : ∀ x ∈ s.pool, ∀ j, j ∉ s.served → p x ≤ 2 * GeneralTPS.thr v p j
  · -- the bag-filling loop
    exact pbagfill_step v p eps hcarrier hn hp heps hs (Finset.Subset.refl _)
      (pfeas_pool v p eps hn hp hs hk0) hB
  · -- the large-good loops
    push_neg at hB
    obtain ⟨g, hg, j0, hj0, hbig⟩ := hB
    -- the slice the claimant asks for is cut out of the price of the expensive good
    have hqle : CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) ≤ p g := by
      have hreq0 : ∀ m, 0 ≤ s.req v p eps m := preq_nonneg v p eps hn hp heps hs
      have h2 : CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) ≤ s.req v p eps j0 :=
        CfgTPS.Qc_empty_le (w := v) (p := p) (k0 := k0) hreq0 j0
      rw [preq_eq_thr v p eps hj0] at h2
      have h3 := GeneralTPS.thr_nonneg v p hn hp j0
      linarith
    exact pshare_step v p eps hcarrier hn hp heps hs k0 hg hqle
end FairSelling.PhaseTPS

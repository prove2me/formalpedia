-- Prove2me | solution 1 for FairSelling.ChargeTPS.feas_pool
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:34:04.587356+00:00
-- url     : https://prove2.me/submissions/18c4e75a-954d-4f5f-9438-0ecb7402420f

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Theorems.Thm_FairSelling_ChargeTPS_req_eq_thr
import Theorems.Thm_FairSelling_CfgTPS_Qc_le_of_gap
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_ChargeTPS_counting_of_cost
import Theorems.Thm_FairSelling_GeneralTPS_thr_nonneg
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_truncBundle_le_vbarSum
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_bundle
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_cash
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_served
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
namespace FairSelling.ChargeTPS
theorem _root_.solution (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) {s : CStage G n} (hs : s.Good v p eps)
    {k0 : Fin n} (hk0 : k0 ∉ s.served) :
    CfgTPS.Feas v p (s.req v p eps) k0 s.bank s.pool ∅ := by
  classical
  have hbank : 0 ≤ s.bank := hs.2.2.2.2.2.2.1
  have hcount := counting_of_cost v p eps hn hp hs k0 hk0
  have hthr : 0 ≤ GeneralTPS.thr v p k0 := GeneralTPS.thr_nonneg v p hn hp k0
  have hcard : (s.served.card : ℝ) ≤ (n : ℝ) - 1 := by
    have h1 : s.served.card < n := by
      have h2 : s.served ⊂ Finset.univ := by
        refine ⟨Finset.subset_univ _, fun h => hk0 (h (Finset.mem_univ k0))⟩
      have := Finset.card_lt_card h2
      simpa using this
    have : (s.served.card : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h1
    linarith
  have hmul : GeneralTPS.thr v p k0
      ≤ (2 * ((n : ℝ) - s.served.card) - 1) * GeneralTPS.thr v p k0 := by
    nlinarith
  have hle : truncBundle (v k0) p (TPS n (v k0) p) s.pool ≤ vbarSum (v k0) p s.pool :=
    truncBundle_le_vbarSum _ _ _ _
  have hreq : s.req v p eps k0 = GeneralTPS.thr v p k0 := req_eq_thr v p eps hk0
  unfold CfgTPS.Feas
  simp only [Finset.sum_empty, add_zero]
  refine CfgTPS.Qc_le_of_gap v p (s.req v p eps) k0 hbank k0 ?_
  rw [hreq]
  linarith
end FairSelling.ChargeTPS

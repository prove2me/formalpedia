-- Prove2me | solution 1 for FairSelling.ChargeTPS.cstep_of_unserved_claimant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:19.333901+00:00
-- url     : https://prove2.me/submissions/8f5b0425-fb3c-495f-a4ce-9f56bc757c33

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Theorems.Thm_FairSelling_ChargeTPS_req_nonneg
import Theorems.Thm_FairSelling_ChargeTPS_req_eq_thr
import Theorems.Thm_FairSelling_ChargeTPS_thr_le_TPS
import Theorems.Thm_FairSelling_ChargeTPS_TPS_le_two_thr
import Theorems.Thm_FairSelling_ChargeTPS_package_of_claimant
import Theorems.Thm_FairSelling_CfgTPS_cost_bound
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_ChargeTPS_step_serve
import Theorems.Thm_FairSelling_restrictVal_mem
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
theorem _root_.solution (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    {s : CStage G n} (hs : s.Good v p eps) {k0 : Fin n}
    {S S₀ : Finset G} (hUP : S ∪ S₀ ⊆ s.pool) (hdisj : Disjoint S S₀)
    (hadm : CfgTPS.Adm v p (s.req v p eps) k0 s.bank S S₀)
    (hmin : ∀ T T₀ : Finset G, T ∪ T₀ ⊆ s.pool → Disjoint T T₀ →
      CfgTPS.Adm v p (s.req v p eps) k0 s.bank T T₀ →
      (S ∪ S₀).card * (s.pool.card + 1) + S₀.card
        ≤ (T ∪ T₀).card * (s.pool.card + 1) + T₀.card)
    {k : Fin n} (hk : k ∉ s.served)
    (hclaim : s.req v p eps k ≤ vbarSum (v k) p S + CfgTPS.Qc v p (s.req v p eps) k0 S) :
    ∃ s' : CStage G n, s'.Good v p eps ∧ s.served.card < s'.served.card := by
  classical
  obtain ⟨S', S₀', q, hS'S, hS₀S₀', hfoot, hdisj', hq0, hqle, hclaim', hkeep, hsafe, hcosteq⟩ :=
    package_of_claimant v p (s.req v p eps) k0 s.bank hp hdisj hadm k hclaim
  have hS'pool : S' ⊆ s.pool :=
    Finset.Subset.trans (Finset.Subset.trans hS'S Finset.subset_union_left) hUP
  have hS₀'pool : S₀' ⊆ s.pool := by
    intro x hx
    exact hUP (hfoot ▸ Finset.mem_union_right S' hx)
  have hbank : 0 ≤ s.bank + (∑ g ∈ S₀', p g) - q - 0 := by linarith
  refine step_serve v p eps heps hs hk hS'pool hS₀'pool hdisj' hq0 le_rfl hbank ?_ hkeep ?_ ?_
  · rw [← req_eq_thr v p eps hk]; exact hclaim'
  · intro j _
    exact hsafe j
  · intro j hj _
    have hreqj : s.req v p eps j = GeneralTPS.thr v p j := req_eq_thr v p eps hj
    have hcost := CfgTPS.cost_bound (w := v) (p := p) (req := s.req v p eps) (k0 := k0)
      (D := s.bank) (P := s.pool) (S := S) (S₀ := S₀)
      (fun i => TPS n (v i) p) j hp hs.2.2.2.2.2.2.1
      (req_nonneg v p eps hn hp heps hs)
      (by rw [hreqj]; exact thr_le_TPS v p hn hp j)
      (by rw [hreqj]; exact TPS_le_two_thr v p hn hp j)
      hUP hdisj hadm hmin
    rw [hreqj] at hcost
    have := hcosteq (TPS n (v j) p) (v j)
    simp only [add_zero]
    linarith
end FairSelling.ChargeTPS

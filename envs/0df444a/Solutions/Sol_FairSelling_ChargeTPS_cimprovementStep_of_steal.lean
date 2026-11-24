-- Prove2me | solution 1 for FairSelling.ChargeTPS.cimprovementStep_of_steal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:44:35.333491+00:00
-- url     : https://prove2.me/submissions/56179d4c-3030-49b0-be13-12288fc61b77

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Theorems.Thm_FairSelling_ChargeTPS_feas_pool
import Theorems.Thm_FairSelling_ChargeTPS_cstep_of_unserved_claimant
import Theorems.Thm_FairSelling_CfgTPS_Qc_claimed
import Theorems.Thm_FairSelling_CfgTPS_exists_min_adm


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
namespace FairSelling.ChargeTPS
theorem _root_.solution (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    (hsteal : CStealStep v p eps) : CImprovementStep v p eps := by
  classical
  intro s hs hfull
  obtain ⟨k0, hk0⟩ : ∃ k0, k0 ∉ s.served := by
    by_contra hcon
    push_neg at hcon
    exact hfull (Finset.eq_univ_of_forall hcon)
  obtain ⟨S, S₀, hUP, hdisj, hadm, hmin⟩ :=
    CfgTPS.exists_min_adm v p (s.req v p eps) k0 s.bank s.pool hp
      (feas_pool v p eps hn hp hs hk0)
  obtain ⟨k, hclaim⟩ := CfgTPS.Qc_claimed v p (s.req v p eps) k0 S
  by_cases hk : k ∈ s.served
  · exact hsteal s k0 hs hk0 S S₀ hUP hdisj hadm hmin k hk hclaim
  · obtain ⟨s', hs', hcard⟩ :=
      cstep_of_unserved_claimant v p eps hn hp heps hs hUP hdisj hadm hmin hk hclaim
    exact ⟨s', hs', Or.inl hcard⟩
end FairSelling.ChargeTPS

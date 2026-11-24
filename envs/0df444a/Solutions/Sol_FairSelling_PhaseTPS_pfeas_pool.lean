-- Prove2me | solution 1 for FairSelling.PhaseTPS.pfeas_pool
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:50:06.649601+00:00
-- url     : https://prove2.me/submissions/6ac94fa6-3429-40c8-8a44-2af115e5de33

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhaseStep
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPhaseImp
import Theorems.Thm_FairSelling_ChargeTPS_feas_pool
import Theorems.Thm_FairSelling_PhaseTPS_PStage_good_toCStage
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_pool


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
namespace FairSelling.PhaseTPS
theorem _root_.solution (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) {s : PStage G n} (hs : s.Good v p eps)
    {k0 : Fin n} (hk0 : k0 ∉ s.served) :
    CfgTPS.Feas v p (s.req v p eps) k0 s.bank s.pool ∅ := by
  have h := ChargeTPS.feas_pool v p eps hn hp (PStage.good_toCStage v p eps hs) (k0 := k0) hk0
  rwa [PStage.toCStage_pool] at h
end FairSelling.PhaseTPS

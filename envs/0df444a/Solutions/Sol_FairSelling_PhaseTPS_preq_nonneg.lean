-- Prove2me | solution 1 for FairSelling.PhaseTPS.preq_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:35.182592+00:00
-- url     : https://prove2.me/submissions/b74fe39d-ea8e-4efc-9aa3-64b948bdaf87

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhaseStep
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPhaseImp
import Theorems.Thm_FairSelling_ChargeTPS_req_nonneg
import Theorems.Thm_FairSelling_PhaseTPS_PStage_good_toCStage


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
namespace FairSelling.PhaseTPS
theorem _root_.solution (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps) {s : PStage G n}
    (hs : s.Good v p eps) (j : Fin n) : 0 ≤ s.req v p eps j :=
  ChargeTPS.req_nonneg v p eps hn hp heps (PStage.good_toCStage v p eps hs) j
end FairSelling.PhaseTPS

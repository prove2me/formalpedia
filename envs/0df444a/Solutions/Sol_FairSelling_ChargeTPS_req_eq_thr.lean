-- Prove2me | solution 1 for FairSelling.ChargeTPS.req_eq_thr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:22:24.50368+00:00
-- url     : https://prove2.me/submissions/e8882bab-47f4-4e7e-9963-6f54813de885

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
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
omit [DecidableEq G]
namespace FairSelling.ChargeTPS
theorem _root_.solution {s : CStage G n} {j : Fin n} (hj : j ∉ s.served) :
    s.req v p eps j = GeneralTPS.thr v p j := by
  simp [CStage.req, hj]
end FairSelling.ChargeTPS

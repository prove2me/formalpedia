-- Prove2me | solution 1 for FairSelling.ChargeTPS.ctotal_le_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:35:31.387211+00:00
-- url     : https://prove2.me/submissions/77bfec5a-4171-417f-afc5-811c98ed4b62

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxGeneral
import Definitions.Def_RequestProject_TPSSefxCharge
import Theorems.Thm_FairSelling_ChargeTPS_good_toStage
import Theorems.Thm_FairSelling_GeneralTPS_total_le_bound


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
namespace FairSelling.ChargeTPS
theorem _root_.solution (hn : 0 < n) (heps : 0 ≤ eps) (hp : ∀ g, 0 ≤ p g) {s : CStage G n}
    (hs : s.Good v p eps) : s.total v p ≤ GeneralTPS.totalBound v p :=
  GeneralTPS.total_le_bound v p eps hp (good_toStage v p eps hn heps hp hs)
end FairSelling.ChargeTPS

-- Prove2me | solution 1 for FairSelling.ChargeTPS.CStage.toStage_pool
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:42:38.790309+00:00
-- url     : https://prove2.me/submissions/42f319a8-6ce3-44a0-8f7b-d665e713e099

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxGeneral
import Definitions.Def_RequestProject_TPSSefxCharge

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.ChargeTPS.CStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
namespace FairSelling.ChargeTPS.CStage
theorem _root_.solution (s : CStage G n) : (s.toStage).pool = s.pool := rfl
end FairSelling.ChargeTPS.CStage

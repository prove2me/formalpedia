-- Prove2me | solution 1 for FairSelling.ChargeTPS.CStage.toStage_cash
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:16:47.892124+00:00
-- url     : https://prove2.me/submissions/1c41dc4d-f607-4b34-aec1-4d590ee6f8c8

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
omit [Fintype G]
namespace FairSelling.ChargeTPS.CStage
theorem _root_.solution (s : CStage G n) : (s.toStage).cash = s.cash := rfl
end FairSelling.ChargeTPS.CStage

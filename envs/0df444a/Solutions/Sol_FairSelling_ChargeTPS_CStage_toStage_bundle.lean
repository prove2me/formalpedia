-- Prove2me | solution 1 for FairSelling.ChargeTPS.CStage.toStage_bundle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:16:44.841079+00:00
-- url     : https://prove2.me/submissions/5a98c629-2f1a-4e52-bcb1-8ab770fe3ec9

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
theorem _root_.solution (s : CStage G n) : (s.toStage).bundle = s.bundle := rfl
end FairSelling.ChargeTPS.CStage

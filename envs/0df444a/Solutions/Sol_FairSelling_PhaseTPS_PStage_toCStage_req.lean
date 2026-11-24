-- Prove2me | solution 1 for FairSelling.PhaseTPS.PStage.toCStage_req
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:44:35.845673+00:00
-- url     : https://prove2.me/submissions/c372ab40-885d-4bdc-a9df-7b257618ee4f

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxPhase

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PhaseTPS.PStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
namespace FairSelling.PhaseTPS.PStage
theorem _root_.solution (s : PStage G n) (j : Fin n) :
    (s.toCStage).req v p eps j = s.req v p eps j := rfl
end FairSelling.PhaseTPS.PStage

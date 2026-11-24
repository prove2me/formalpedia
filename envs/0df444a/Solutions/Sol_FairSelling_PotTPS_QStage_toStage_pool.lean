-- Prove2me | solution 1 for FairSelling.PotTPS.QStage.toStage_pool
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:45:54.522684+00:00
-- url     : https://prove2.me/submissions/c47ba00b-1fcf-4a19-b5b1-fac562f2d1ad

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PotTPS.QStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
variable {v p eps}
namespace FairSelling.PotTPS.QStage
theorem _root_.solution (s : QStage G n) : (s.toStage).pool = s.pool := rfl
end FairSelling.PotTPS.QStage

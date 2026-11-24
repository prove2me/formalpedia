-- Prove2me | solution 1 for FairSelling.PhaseTPS.PStage.toCStage_pool
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:45:24.093615+00:00
-- url     : https://prove2.me/submissions/bebd1541-d3e9-43f7-af95-edf438d39de5

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxPhase
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_soldSet

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PhaseTPS.PStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
namespace FairSelling.PhaseTPS.PStage
theorem _root_.solution (s : PStage G n) : (s.toCStage).pool = s.pool := by
  unfold ChargeTPS.CStage.pool PStage.pool
  rw [toCStage_soldSet]
  rfl
end FairSelling.PhaseTPS.PStage

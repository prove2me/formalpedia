-- Prove2me | solution 1 for FairSelling.PhaseTPS.PStage.toCStage_cash
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:20:53.559888+00:00
-- url     : https://prove2.me/submissions/da02589d-d629-4e1b-b81f-d7cc0247f441

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
omit [Fintype G]
namespace FairSelling.PhaseTPS.PStage
theorem _root_.solution (s : PStage G n) : (s.toCStage).cash = s.cash := rfl
end FairSelling.PhaseTPS.PStage

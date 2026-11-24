-- Prove2me | solution 1 for FairSelling.PhaseTPS.PStage.toCStage_bank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:21:51.692799+00:00
-- url     : https://prove2.me/submissions/537d844e-33c9-449f-bb12-b0cf2dd3201d

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
theorem _root_.solution (s : PStage G n) : (s.toCStage).bank = s.bank := rfl
end FairSelling.PhaseTPS.PStage

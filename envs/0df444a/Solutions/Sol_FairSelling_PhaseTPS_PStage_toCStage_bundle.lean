-- Prove2me | solution 1 for FairSelling.PhaseTPS.PStage.toCStage_bundle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:21:12.332408+00:00
-- url     : https://prove2.me/submissions/2ad27c93-b379-44ac-a4c3-b70bff4dc394

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
theorem _root_.solution (s : PStage G n) : (s.toCStage).bundle = s.bundle := rfl
end FairSelling.PhaseTPS.PStage

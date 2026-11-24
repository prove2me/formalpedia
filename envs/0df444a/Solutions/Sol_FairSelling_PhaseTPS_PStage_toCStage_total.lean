-- Prove2me | solution 1 for FairSelling.PhaseTPS.PStage.toCStage_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:44:36.339697+00:00
-- url     : https://prove2.me/submissions/1426bfc4-f24b-4194-9833-48b4b96b7224

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
theorem _root_.solution (s : PStage G n) : (s.toCStage).total v p = s.total v p := rfl
end FairSelling.PhaseTPS.PStage

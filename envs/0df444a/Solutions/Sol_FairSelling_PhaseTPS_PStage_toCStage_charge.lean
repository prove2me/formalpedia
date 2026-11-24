-- Prove2me | solution 1 for FairSelling.PhaseTPS.PStage.toCStage_charge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:31:31.530374+00:00
-- url     : https://prove2.me/submissions/77f09924-c559-4d65-8c2d-4754e9864c87

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
open Classical
namespace FairSelling.PhaseTPS.PStage
theorem _root_.solution (s : PStage G n) (i : Fin n) :
    (s.toCStage).charge i = s.own i ∪ (s.ext i).filter (fun g => ∀ k, g ∈ s.charge k → i ≤ k) :=
  rfl
end FairSelling.PhaseTPS.PStage

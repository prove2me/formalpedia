-- Prove2me | solution 1 for FairSelling.PotTPS.QStage.toStage_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:46:05.40222+00:00
-- url     : https://prove2.me/submissions/e2d00007-95dd-458b-94f0-920e1ba6caca

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
omit [Fintype G]
namespace FairSelling.PotTPS.QStage
theorem _root_.solution (s : QStage G n) : (s.toStage).total v p = s.total v p := rfl
end FairSelling.PotTPS.QStage

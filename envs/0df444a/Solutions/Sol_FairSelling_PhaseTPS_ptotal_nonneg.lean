-- Prove2me | solution 1 for FairSelling.PhaseTPS.ptotal_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:37.960916+00:00
-- url     : https://prove2.me/submissions/23e6037f-f6db-4f36-8318-07fb1852b645

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxPhase
import Theorems.Thm_FairSelling_PhaseTPS_PStage_good_toCStage
import Theorems.Thm_FairSelling_ChargeTPS_ctotal_nonneg


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
namespace FairSelling.PhaseTPS
theorem _root_.solution (hn : 0 < n) (heps : 0 ≤ eps) (hp : ∀ g, 0 ≤ p g) {s : PStage G n}
    (hs : s.Good v p eps) : 0 ≤ s.total v p :=
  ChargeTPS.ctotal_nonneg v p eps hn heps hp (PStage.good_toCStage v p eps hs)
end FairSelling.PhaseTPS

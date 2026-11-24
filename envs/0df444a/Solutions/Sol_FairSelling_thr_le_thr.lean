-- Prove2me | solution 1 for FairSelling.thr_le_thr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:10:27.627398+00:00
-- url     : https://prove2.me/submissions/1f450f84-edbd-4567-b778-8a1cfb05c969

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_EquiMMS
import Definitions.Def_RequestProject_TwoThirdsLoss

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) {i j : Fin n}
    (h : MMS n (v i) p ≤ MMS n (v j) p) : thr v p i ≤ thr v p j := by
  unfold thr rho
  have : (0:ℝ) ≤ 2 / 3 := by norm_num
  nlinarith
end FairSelling

-- Prove2me | solution 1 for FairSelling.ChargeTPS.CStage.disjoint_pool_charge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:59:15.766789+00:00
-- url     : https://prove2.me/submissions/2f07513e-370a-40d8-ba0a-e796535e2b73

import Mathlib
import Definitions.Def_RequestProject_TPSSefxCharge
import Definitions.Def_RequestProject_TPSSefxServe
import Theorems.Thm_FairSelling_ChargeTPS_CStage_disjoint_pool_soldSet

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.ChargeTPS.CStage
namespace FairSelling.ChargeTPS.CStage
theorem _root_.solution (s : CStage G n) (i : Fin n) : Disjoint s.pool (s.charge i) :=
  Finset.disjoint_left.mpr (fun _ hx hx' =>
    Finset.disjoint_left.mp (disjoint_pool_soldSet s) hx
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx'⟩))
end FairSelling.ChargeTPS.CStage

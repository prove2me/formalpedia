-- Prove2me | solution 1 for FairSelling.PhaseTPS.PStage.disjoint_pool_charge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:46:14.905694+00:00
-- url     : https://prove2.me/submissions/93e918e7-98eb-44ed-8712-ce59f2ebb526

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxPhase
import Theorems.Thm_FairSelling_PhaseTPS_PStage_disjoint_pool_sold

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PhaseTPS.PStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
namespace FairSelling.PhaseTPS.PStage
theorem _root_.solution (s : PStage G n) (i : Fin n) : Disjoint s.pool (s.charge i) :=
  Finset.disjoint_left.mpr (fun _ hx hx' =>
    Finset.disjoint_left.mp (disjoint_pool_sold s) hx
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx'⟩))
end FairSelling.PhaseTPS.PStage

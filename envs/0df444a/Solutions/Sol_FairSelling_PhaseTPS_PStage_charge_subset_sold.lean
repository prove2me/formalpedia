-- Prove2me | solution 1 for FairSelling.PhaseTPS.PStage.charge_subset_sold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:44:52.807921+00:00
-- url     : https://prove2.me/submissions/e0fdbefc-42a9-4439-b918-a601a6709315

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
theorem _root_.solution (s : PStage G n) (i : Fin n) : s.charge i ⊆ s.sold :=
  fun _ hx => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩
end FairSelling.PhaseTPS.PStage

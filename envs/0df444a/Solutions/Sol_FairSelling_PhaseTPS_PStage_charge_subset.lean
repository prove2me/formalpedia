-- Prove2me | solution 1 for FairSelling.PhaseTPS.PStage.charge_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:58:32.744753+00:00
-- url     : https://prove2.me/submissions/c40668a6-676b-49b5-b4a9-70675d1e4efd

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxPhase
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_charge

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
theorem _root_.solution (s : PStage G n) (i : Fin n) : (s.toCStage).charge i ⊆ s.charge i := by
  classical
  intro x hx
  rw [toCStage_charge] at hx
  rcases Finset.mem_union.mp hx with h | h
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ (Finset.mem_of_mem_filter _ h)
end FairSelling.PhaseTPS.PStage

-- Prove2me | solution 1 for FairSelling.PotTPS.QStage.src_subset_cutSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:45:28.501473+00:00
-- url     : https://prove2.me/submissions/4b51d47a-b910-4a71-9ea5-36a88ac700dd

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
import Theorems.Thm_FairSelling_PotTPS_QStage_mem_cutSet

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PotTPS.QStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
omit [Fintype G]
namespace FairSelling.PotTPS.QStage
theorem _root_.solution (s : QStage G n) (i : Fin n) : s.src i ⊆ s.cutSet :=
  fun _ hg => mem_cutSet hg
end FairSelling.PotTPS.QStage

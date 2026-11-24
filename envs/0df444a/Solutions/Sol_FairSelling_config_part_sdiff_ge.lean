-- Prove2me | solution 1 for FairSelling.config_part_sdiff_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:08:45.627511+00:00
-- url     : https://prove2.me/submissions/17c71d9b-6f54-411d-9b0c-8a98e4eb8e5f

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_ConfigSplit
import Theorems.Thm_FairSelling_vbarSum_sdiff_inter

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {A : Fin 3 → Finset G} {s : Finset G} {q : Fin 3 → ℝ} {r : ℝ}
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hcfg : ConfigN 3 w p r A s q) (X : Finset G)
    (j : Fin 3) :
    r - q j - vbarSum w p (A j ∩ X) ≤ vbarSum w p (A j \ X) := by
  have h := hcfg.2.2.2.2.2 j
  rw [vbarSum_sdiff_inter]
  linarith
end FairSelling

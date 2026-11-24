-- Prove2me | solution 1 for FairSelling.config_two_parts_sdiff_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:08:47.300956+00:00
-- url     : https://prove2.me/submissions/9dfbd5d7-6a3a-45b3-b801-ce52ef02a180

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_ConfigSplit
import Theorems.Thm_FairSelling_vbarSum_sdiff_inter
import Theorems.Thm_FairSelling_vbarSum_union


set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {A : Fin 3 → Finset G} {s : Finset G} {q : Fin 3 → ℝ} {r : ℝ}
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hcfg : ConfigN 3 w p r A s q) (X : Finset G)
    {j' j'' : Fin 3} (h : j' ≠ j'') :
    2 * r - q j' - q j'' - vbarSum w p ((A j' ∪ A j'') ∩ X)
      ≤ vbarSum w p ((A j' ∪ A j'') \ X) := by
  have h1 := hcfg.2.2.2.2.2 j'
  have h2 := hcfg.2.2.2.2.2 j''
  have hu : vbarSum w p (A j' ∪ A j'') = vbarSum w p (A j') + vbarSum w p (A j'') :=
    vbarSum_union w p (hcfg.1 j' j'' h)
  rw [vbarSum_sdiff_inter, hu]
  linarith
end FairSelling

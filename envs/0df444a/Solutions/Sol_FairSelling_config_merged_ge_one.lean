-- Prove2me | solution 1 for FairSelling.config_merged_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:04:07.548311+00:00
-- url     : https://prove2.me/submissions/c00046d3-8de5-4b88-8f79-c0f26fd66ca3

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_ConfigSplit
import Theorems.Thm_FairSelling_config_part_sdiff_ge

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {A : Fin 3 → Finset G} {s : Finset G} {q : Fin 3 → ℝ} {r : ℝ}
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hcfg : ConfigN 3 w p r A s q)
    (X : Finset G) {j' j'' k : Fin 3} (hk : k = j' ∨ k = j'') :
    r - q k - vbarSum w p (A k ∩ X) ≤ vbarSum w p ((A j' ∪ A j'') \ X) := by
  have hsub : A k \ X ⊆ (A j' ∪ A j'') \ X := by
    refine Finset.sdiff_subset_sdiff ?_ (le_refl X)
    rcases hk with rfl | rfl
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
  have hmono : vbarSum w p (A k \ X) ≤ vbarSum w p ((A j' ∪ A j'') \ X) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun g _ _ => le_trans (hw g) (le_max_right _ _))
  have := config_part_sdiff_ge w p hcfg X k
  linarith
end FairSelling

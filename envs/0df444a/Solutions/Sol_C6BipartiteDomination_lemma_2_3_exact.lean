-- Prove2me | solution 1 for C6BipartiteDomination.lemma_2_3_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:44:41.078816+00:00
-- url     : https://prove2.me/submissions/34dc532b-737d-4f52-8ccd-edf449d950c9

import Definitions.Def_C6BipartiteDomination_Basic
import Definitions.Def_C6BipartiteDomination_A2
import Theorems.Thm_C6BipartiteDomination_isolatedSubset_dominates_region
import Theorems.Thm_C6BipartiteDomination_responsibilityRegion_irreducible

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D X : Finset V}
    (hD : MinimumBipartiteDominatingSet G D)
    (hX : IsolatedSubset G D X) :
    BipartiteDominatingOn G (responsibilityRegion G D X) X ∧
      ∀ Y, BipartiteDominatingOn G (responsibilityRegion G D X) Y → X.card ≤ Y.card := by
  refine ⟨isolatedSubset_dominates_region G hD.1 hX, ?_⟩
  intro Y hY
  exact responsibilityRegion_irreducible G hD hX hY
end C6BipartiteDomination

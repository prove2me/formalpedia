-- Prove2me | solution 1 for C6BipartiteDomination.paper11K4_resource_eq_owner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:09:33.721077+00:00
-- url     : https://prove2.me/submissions/11c58c9f-ecbf-475b-bcc1-cf69bdc90e9e

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_paper11OwnerCompensation_eq_K4

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ u ∈ paper11K4RightVertices G D hCan hmax,
      paper11K4Resource G D hCan hmax u) =
      ∑ u ∈ paper11K4RightVertices G D hCan hmax,
        paper11OwnerResource G D hCan hmax u := by
  apply Finset.sum_congr rfl
  intro u hu
  simp only [paper11K4Resource, paper11OwnerResource]
  rw [paper11OwnerCompensation_eq_K4 G hCan hmax hu]
end C6BipartiteDomination

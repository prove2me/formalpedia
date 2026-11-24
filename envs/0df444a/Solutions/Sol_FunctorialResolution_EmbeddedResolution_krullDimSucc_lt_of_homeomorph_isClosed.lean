-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.krullDimSucc_lt_of_homeomorph_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:06:53.884853+00:00
-- url     : https://prove2.me/submissions/6f32ef77-dd06-48b0-9959-ef1766cb50e3

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_KrullDimClosedSubset
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_topologicalKrullDim_lt_of_isClosed_of_not_subset_irreducibleComponents
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_topologicalKrullDim_eq_of_homeomorph
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_krullDimSucc_lt_of_topologicalKrullDim_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open TopologicalSpace AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (X Z : Scheme.{u}) (Y : Set ↥X)
    (hY : IsClosed Y) (hne : Y.Nonempty)
    (hcomp : ∀ C ∈ irreducibleComponents ↥X, ¬ C ⊆ Y)
    (hfin : topologicalKrullDim ↥X < ⊤)
    (e : ↥Z ≃ₜ ↥Y) :
    krullDimSucc Z < krullDimSucc X := by
  have h := topologicalKrullDim_lt_of_isClosed_of_not_subset_irreducibleComponents Y hY hne hcomp
    hfin
  refine krullDimSucc_lt_of_topologicalKrullDim_lt Z X ?_ hfin
  rw [topologicalKrullDim_eq_of_homeomorph e]
  exact h
end FunctorialResolution.EmbeddedResolution

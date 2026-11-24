-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isClosed_of_maximal_irreducible_subset_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:04:49.378966+00:00
-- url     : https://prove2.me/submissions/50345918-2090-4e1d-8f9d-661e1e4f178b

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisibility
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} (D : X.IdealSheafData)
    {C : Set X} (hC : IsIrreducible C) (hCsub : C ⊆ (D.support : Set X))
    (hCmax : ∀ C' : Set X, IsIrreducible C' → C ⊆ C' → C' ⊆ (D.support : Set X) → C' = C) :
    IsClosed C := by
  have hsupp : IsClosed ((D.support : Set X)) := D.support.2
  have hsub : closure C ⊆ (D.support : Set X) := closure_minimal hCsub hsupp
  have heq : closure C = C := hCmax (closure C) hC.closure subset_closure hsub
  rw [← heq]
  exact isClosed_closure
end FunctorialResolution.EmbeddedResolution

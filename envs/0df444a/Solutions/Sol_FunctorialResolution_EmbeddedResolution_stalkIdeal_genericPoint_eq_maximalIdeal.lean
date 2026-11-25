-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.stalkIdeal_genericPoint_eq_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:24:33.610955+00:00
-- url     : https://prove2.me/submissions/92ce3e1d-41a4-4e33-bb51-c9ca167db3e7

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisibility
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_eq_maximalIdeal_of_minimal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_etaleChart_genericPoint_mem

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
variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (D : X.IdealSheafData)
    (hloc : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j})
    {C : Set X} (hC : IsIrreducible C) (hCsub : C ⊆ (D.support : Set X))
    (hCmax : ∀ C' : Set X, IsIrreducible C' → C ⊆ C' → C' ⊆ (D.support : Set X) → C' = C) :
    stalkIdeal D hC.genericPoint =
      IsLocalRing.maximalIdeal (X.presheaf.stalk hC.genericPoint) := by
  obtain ⟨x, hx⟩ := hC.1
  obtain ⟨V, hV, hxV, hηV, n, c, j, hD, hspec, hηs, hmin⟩ :=
    exists_etaleChart_genericPoint_mem p D hloc hC hCsub hCmax x hx
  exact stalkIdeal_eq_maximalIdeal_of_minimal p hV c j D hD x hC.genericPoint hxV hηV hspec
    hηs hmin
end FunctorialResolution.EmbeddedResolution

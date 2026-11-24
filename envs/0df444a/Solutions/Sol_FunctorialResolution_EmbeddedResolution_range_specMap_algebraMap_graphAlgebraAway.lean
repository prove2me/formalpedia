-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.range_specMap_algebraMap_graphAlgebraAway
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:03:36.165476+00:00
-- url     : https://prove2.me/submissions/5c6f45e3-436c-4f17-81ed-2135b3caaea4

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphAlgebra
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphAlgebraStandardSmooth
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphAlgebraSpecSmooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open CategoryTheory AlgebraicGeometry
variable {R : Type u} [CommRing R] {σ τ : Type u} [Fintype τ] [DecidableEq τ]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution
    (f : τ → MvPolynomial σ R) (v : τ → σ) :
    Set.range ⇑(Spec.map
        (CommRingCat.ofHom (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v)))).base =
      (PrimeSpectrum.basicOpen (graphJacobianMinorDet f v) : Set (PrimeSpectrum (GraphAlgebra f))) := by
  have h := PrimeSpectrum.localization_away_comap_range (R := GraphAlgebra f)
    (GraphAlgebraAway f v) (graphJacobianMinorDet f v)
  exact h
end FunctorialResolution.EmbeddedResolution

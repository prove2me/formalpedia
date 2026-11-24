-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.awayCoordGenEquivMvPolynomial_symm_comp_coordBlowupSubst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:04:05.284376+00:00
-- url     : https://prove2.me/submissions/e355ee4e-2f9b-4f63-a95b-f89e7a27ecc5

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupUniversalLift
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupChartPreimages
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_CoordinateBlowupChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
universe u v
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (R : Type u) [CommRing R] {σ : Type v} [DecidableEq σ]
    (S : Finset σ) (s : σ) (hs : s ∈ S) :
    (awayCoordGenEquivMvPolynomial R S s hs).symm.toRingHom.comp (coordBlowupSubst R S s).toRingHom
      = Blowup.chartRingHom (coordIdeal R S) (coordIdealGen R S s hs) :=
  (exists_ringEquiv_away_mvPolynomial R S s hs).choose_spec
end FunctorialResolution.EmbeddedResolution

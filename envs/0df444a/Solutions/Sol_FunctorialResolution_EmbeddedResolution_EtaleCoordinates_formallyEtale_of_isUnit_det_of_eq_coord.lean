-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.formallyEtale_of_isUnit_det_of_eq_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:30:00.469265+00:00
-- url     : https://prove2.me/submissions/5e071c30-2d23-4900-9802-1fc519e0161c

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_JacobianCriterion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_FormallyEtaleCoordinates
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_formallyEtale_of_isUnit_det


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
namespace FunctorialResolution.EmbeddedResolution.EtaleCoordinates
theorem _root_.solution (k : Type*) [CommRing k] (ι : Type*) [Fintype ι]
    [DecidableEq ι] (T : Type*) [CommRing T] [Algebra k T] [Algebra (MvPolynomial ι k) T]
    [IsScalarTower k (MvPolynomial ι k) T] [Algebra.FormallySmooth k T]
    (e : Module.Basis ι T (KaehlerDifferential k T)) (w : ι → T)
    (hw : ∀ i : ι, w i = JacobianCriterion.coord k ι T i)
    (hdet : IsUnit (e.det fun i : ι => KaehlerDifferential.D k T (w i))) :
    Algebra.FormallyEtale (MvPolynomial ι k) T := by
  have hfun : (fun i : ι => KaehlerDifferential.D k T (JacobianCriterion.coord k ι T i)) =
      fun i : ι => KaehlerDifferential.D k T (w i) := by
    funext i
    rw [hw i]
  have h : IsUnit (e.det fun i : ι =>
      KaehlerDifferential.D k T (JacobianCriterion.coord k ι T i)) := by
    rw [hfun]
    exact hdet
  exact JacobianCriterion.formallyEtale_of_isUnit_det k ι T e h
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates

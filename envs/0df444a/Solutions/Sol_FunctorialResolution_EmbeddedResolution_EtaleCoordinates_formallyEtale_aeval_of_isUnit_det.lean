-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.formallyEtale_aeval_of_isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:47:11.651937+00:00
-- url     : https://prove2.me/submissions/7a05102b-a728-4837-9401-6eed1184fa70

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_JacobianCriterion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_FormallyEtaleCoordinates
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_formallyEtale_of_isUnit_det_of_eq_coord

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
theorem _root_.solution {k : Type*} [CommRing k] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {T : Type*} [CommRing T] [Algebra k T] [Algebra.FormallySmooth k T]
    (e : Module.Basis ι T (KaehlerDifferential k T)) (w : ι → T)
    (hdet : IsUnit (e.det fun i : ι => KaehlerDifferential.D k T (w i))) :
    letI : Algebra (MvPolynomial ι k) T :=
      (MvPolynomial.aeval w : MvPolynomial ι k →ₐ[k] T).toRingHom.toAlgebra
    Algebra.FormallyEtale (MvPolynomial ι k) T := by
  let instAeval : Algebra (MvPolynomial ι k) T :=
    (MvPolynomial.aeval w : MvPolynomial ι k →ₐ[k] T).toRingHom.toAlgebra
  have hmap : ∀ p : MvPolynomial ι k,
      algebraMap (MvPolynomial ι k) T p = MvPolynomial.aeval w p := fun _ => rfl
  have instTower : IsScalarTower k (MvPolynomial ι k) T :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [hmap, MvPolynomial.algebraMap_eq, MvPolynomial.aeval_C]
  show Algebra.FormallyEtale (MvPolynomial ι k) T
  refine formallyEtale_of_isUnit_det_of_eq_coord k ι T e w (fun i => ?_) hdet
  show w i = algebraMap (MvPolynomial ι k) T (MvPolynomial.X i)
  rw [hmap, MvPolynomial.aeval_X]
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates

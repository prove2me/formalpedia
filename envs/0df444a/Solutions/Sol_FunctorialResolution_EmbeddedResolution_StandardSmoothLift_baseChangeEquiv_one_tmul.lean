-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.StandardSmoothLift.baseChangeEquiv_one_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:47:46.963142+00:00
-- url     : https://prove2.me/submissions/ee1f849e-bd80-4dab-87ee-edd19e789c01

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_StandardSmoothLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open scoped TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.StandardSmoothLift
universe u
variable {S R B : Type u} [CommRing S] [CommRing R] [CommRing B]
  [Algebra S R] [Algebra R B] {ι σ : Type} [Finite σ]
  (hsurj : Function.Surjective (algebraMap S R))
  (P : Algebra.SubmersivePresentation R B ι σ)
variable [Algebra S B] [IsScalarTower S R B]
namespace FunctorialResolution.EmbeddedResolution.StandardSmoothLift
theorem _root_.solution (b' : LiftedAlgebra hsurj P) :
    baseChangeEquiv hsurj P (1 ⊗ₜ[S] b') = liftedAlgebraHom hsurj P b' := by
  have h : baseChangeEquiv hsurj P (1 ⊗ₜ[S] b')
      = (Algebra.ofId R B) (1 : R) * liftedAlgebraHom hsurj P b' := rfl
  rw [h, map_one, one_mul]
end FunctorialResolution.EmbeddedResolution.StandardSmoothLift

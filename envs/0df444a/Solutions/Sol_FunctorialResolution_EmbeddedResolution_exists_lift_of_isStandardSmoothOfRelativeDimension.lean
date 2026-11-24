-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_lift_of_isStandardSmoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:01:27.853654+00:00
-- url     : https://prove2.me/submissions/934f8a11-06bf-453c-9ad1-f9e18ac7898c

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_StandardSmoothLift
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_StandardSmoothLiftRelativeDimension
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_StandardSmoothLift_liftedSubmersivePresentation_dimension
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_StandardSmoothLift_baseChangeEquiv_one_tmul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open scoped TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (S R B : Type u) [CommRing S] [CommRing R] [CommRing B]
  [Algebra S R] [Algebra R B] [Algebra S B] [IsScalarTower S R B]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (r : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r R B]
    (hsurj : Function.Surjective (algebraMap S R)) :
    ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra S B') (f : B' →ₐ[S] B),
      Algebra.IsStandardSmoothOfRelativeDimension r S B' ∧ Function.Surjective f ∧
        ∃ e : (R ⊗[S] B') ≃ₐ[R] B, ∀ b' : B', e (1 ⊗ₜ[S] b') = f b' := by
  have hinst : Algebra.IsStandardSmoothOfRelativeDimension r R B := ‹_›
  obtain ⟨ι, σ, hσ, hι, P, hdim⟩ := hinst.out
  have : Finite ι := hι
  have : Finite σ := hσ
  refine ⟨StandardSmoothLift.LiftedAlgebra hsurj P, inferInstance, inferInstance,
    StandardSmoothLift.liftedAlgebraHom hsurj P, ?_,
    StandardSmoothLift.liftedAlgebraHom_surjective hsurj P,
    StandardSmoothLift.baseChangeEquiv hsurj P,
    StandardSmoothLift.baseChangeEquiv_one_tmul hsurj P⟩
  exact ⟨⟨Unit ⊕ ι, Unit ⊕ σ, inferInstance, inferInstance,
    StandardSmoothLift.liftedSubmersivePresentation hsurj P,
    (StandardSmoothLift.liftedSubmersivePresentation_dimension hsurj P).trans hdim⟩⟩
end FunctorialResolution.EmbeddedResolution

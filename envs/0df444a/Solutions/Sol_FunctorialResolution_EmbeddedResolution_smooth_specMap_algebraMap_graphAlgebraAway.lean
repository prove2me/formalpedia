-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.smooth_specMap_algebraMap_graphAlgebraAway
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:06:56.35448+00:00
-- url     : https://prove2.me/submissions/63c09a61-eaf3-4e56-b955-ee027390458d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphAlgebra
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphAlgebraStandardSmooth
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphAlgebraSpecSmooth
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isStandardSmooth_graphAlgebraAway


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
theorem _root_.solution [Fintype σ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial τ R) (GraphAlgebraAway f v)))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  have : Algebra.IsStandardSmooth (MvPolynomial τ R) (GraphAlgebraAway f v) :=
    isStandardSmooth_graphAlgebraAway f v hv
  show @Algebra.Smooth _ _ _ _ (algebraMap (MvPolynomial τ R) (GraphAlgebraAway f v)).toAlgebra
  have h : (algebraMap (MvPolynomial τ R) (GraphAlgebraAway f v)).toAlgebra =
      (inferInstance : Algebra (MvPolynomial τ R) (GraphAlgebraAway f v)) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  rw [h]
  refine ⟨?_, ?_⟩ <;> infer_instance
end FunctorialResolution.EmbeddedResolution

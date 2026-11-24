-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.graphPreSubmersivePresentation_jacobiMatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:49:09.74256+00:00
-- url     : https://prove2.me/submissions/7711f644-2d07-4389-8b35-0527c91c5566

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphAlgebra
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_graphPreSubmersivePresentation_relation
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_graphPreSubmersivePresentation_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_graphJacobianMinorMatrix_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.graphPreSubmersivePresentation_relation
attribute [local simp] FunctorialResolution.EmbeddedResolution.graphPreSubmersivePresentation_map

set_option autoImplicit false
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {R : Type u} [CommRing R] {σ τ : Type u}
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution [Fintype τ] [DecidableEq τ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    (graphPreSubmersivePresentation f v hv).jacobiMatrix
      = -((graphJacobianMinorMatrix f v).map
          (fun p => MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) p)) := by
  ext i j
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  simp only [graphPreSubmersivePresentation_relation, graphPreSubmersivePresentation_map,
    graphRelation, map_sub, MvPolynomial.pderiv_C, MvPolynomial.pderiv_map, zero_sub,
    Matrix.neg_apply, Matrix.map_apply, graphJacobianMinorMatrix_apply]
end FunctorialResolution.EmbeddedResolution

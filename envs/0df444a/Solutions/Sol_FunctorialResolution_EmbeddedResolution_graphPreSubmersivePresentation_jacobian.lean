-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.graphPreSubmersivePresentation_jacobian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:02:39.991412+00:00
-- url     : https://prove2.me/submissions/0d0fd400-b2e2-40e5-b08f-1992b7d94bb8

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphAlgebra
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_graphPreSubmersivePresentation_jacobiMatrix

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
variable {R : Type u} [CommRing R] {σ τ : Type u}
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution [Fintype τ] [DecidableEq τ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    (graphPreSubmersivePresentation f v hv).jacobian
      = (-1 : GraphAlgebra f) ^ Fintype.card τ * graphAlgebraEquiv f (graphJacobianMinorMatrix f v).det := by
  have hmap : ((graphJacobianMinorMatrix f v).map
      (fun p => MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) p)).det
      = MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) (graphJacobianMinorMatrix f v).det :=
    (RingHom.map_det (MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R))
      (graphJacobianMinorMatrix f v)).symm
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    graphPreSubmersivePresentation_jacobiMatrix, Matrix.det_neg, hmap, map_mul, map_pow,
    map_neg, map_one]
  congr 1
  exact graphAlgebraAeval_map_C f _
end FunctorialResolution.EmbeddedResolution

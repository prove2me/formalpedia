-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.form_norm_orthonormal_coords
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:05.639393+00:00
-- url     : https://prove2.me/submissions/08ae9252-8f80-4f29-ae89-8bff0582798c

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x6
open Module
variable {K : Type} [Field K] {σ : K →+* K}
namespace Formalism.FourierDecayAlt.P.S3x6
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] {h : V →ₛₗ[σ] V →ₗ[K] K} {n : ℕ}
    (b : Basis (Fin n) K V) (hb : Ortho h b) (v : V) :
    h v v = ∑ i, σ (b.equivFun v i) * b.equivFun v i := by
  conv_lhs => rw [← b.sum_equivFun v]
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    RingHom.id_apply, hb _ _]
  simp [mul_comm]
end Formalism.FourierDecayAlt.P.S3x6

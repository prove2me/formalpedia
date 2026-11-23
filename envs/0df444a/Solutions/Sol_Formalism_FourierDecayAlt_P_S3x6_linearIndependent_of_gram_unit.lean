-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.linearIndependent_of_gram_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:51.251318+00:00
-- url     : https://prove2.me/submissions/3cdbf62c-e604-4305-a524-3eac7c561512

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_gram_mulVec_eq

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
variable {V : Type} [AddCommGroup V] [Module K V]
namespace Formalism.FourierDecayAlt.P.S3x6
theorem _root_.solution (h : V →ₛₗ[σ] V →ₗ[K] K) {κ : Type} [Fintype κ] [DecidableEq κ] (z : κ → V)
    (hG : IsUnit (gramMatrix h z).det) : LinearIndependent K z := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h1 : (gramMatrix h z).mulVec c = 0 := by
    ext i
    rw [gram_mulVec_eq, hc]
    simp
  have h2 : Function.Injective (gramMatrix h z).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hG)
  have h3 : c = 0 := h2 (by rw [h1, Matrix.mulVec_zero])
  intro i
  rw [h3]; rfl
end Formalism.FourierDecayAlt.P.S3x6

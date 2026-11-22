-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.gram_mulVec_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:11:22.198484+00:00
-- url     : https://prove2.me/submissions/0e413d05-8eeb-473c-bf73-d8aa7e24234f

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_form_sum_right_alt

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
theorem _root_.solution (h : V →ₛₗ[σ] V →ₗ[K] K) {ι : Type} [Fintype ι] (x : ι → V) (c : ι → K)
    (i : ι) : (gramMatrix h x).mulVec c i = h (x i) (∑ j, c j • x j) := by
  rw [form_sum_right_alt]
  simp [gramMatrix, Matrix.mulVec, dotProduct, mul_comm]
end Formalism.FourierDecayAlt.P.S3x6

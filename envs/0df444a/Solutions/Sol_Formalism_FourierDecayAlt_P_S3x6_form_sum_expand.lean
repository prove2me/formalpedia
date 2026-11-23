-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.form_sum_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:29.317959+00:00
-- url     : https://prove2.me/submissions/eed1f5a6-c7d2-4c57-9cce-d85ccde99b0b

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_form_sum_right_alt
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_form_sum_left_alt

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
theorem _root_.solution (h : V →ₛₗ[σ] V →ₗ[K] K) {κ : Type} [Fintype κ] (b : κ → V) (c d : κ → K) :
    h (∑ i, c i • b i) (∑ j, d j • b j) = ∑ i, ∑ j, σ (c i) * (d j * h (b i) (b j)) := by
  rw [form_sum_left_alt]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [form_sum_right_alt, Finset.mul_sum]
end Formalism.FourierDecayAlt.P.S3x6

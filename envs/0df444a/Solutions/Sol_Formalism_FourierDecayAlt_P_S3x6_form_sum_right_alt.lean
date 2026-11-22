-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.form_sum_right_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:28:41.145243+00:00
-- url     : https://prove2.me/submissions/faf7c543-eab4-4312-8aa7-92633bcb315a

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
variable {V : Type} [AddCommGroup V] [Module K V]
namespace Formalism.FourierDecayAlt.P.S3x6
theorem _root_.solution (h : V →ₛₗ[σ] V →ₗ[K] K) {ι : Type} [Fintype ι] (u : V) (c : ι → K)
    (x : ι → V) : h u (∑ j, c j • x j) = ∑ j, c j * h u (x j) := by
  simp [map_sum]
end Formalism.FourierDecayAlt.P.S3x6

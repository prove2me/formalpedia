-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.form_sum_left_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:10:28.785805+00:00
-- url     : https://prove2.me/submissions/913b26dc-2fa8-4dac-9c19-0c71cb3de2a2

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
    (x : ι → V) : h (∑ j, c j • x j) u = ∑ j, σ (c j) * h (x j) u := by
  simp [map_sum, LinearMap.sum_apply]
end Formalism.FourierDecayAlt.P.S3x6

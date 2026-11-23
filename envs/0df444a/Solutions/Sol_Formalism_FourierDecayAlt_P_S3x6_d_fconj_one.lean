-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.d_fconj_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:58.315728+00:00
-- url     : https://prove2.me/submissions/26863f25-b474-4890-b536-5f2d3383c4b5

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_d_fconj_eq

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
open Matrix Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.S3x6
theorem _root_.solution {q : ℕ} (hσ : ∀ x, σ x = x ^ q) {α : Type} [DecidableEq α] :
    fconj q (1 : Matrix α α K) = 1 := by
  rw [d_fconj_eq hσ, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]
end Formalism.FourierDecayAlt.P.S3x6

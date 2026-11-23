-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.d_fconj_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:10.273526+00:00
-- url     : https://prove2.me/submissions/0acdc300-96b8-4a11-9296-3d1808a73921

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
theorem _root_.solution {q : ℕ} (hσ : ∀ x, σ x = x ^ q) {α β γ : Type} [Fintype β] (X : Matrix α β K)
    (Y : Matrix β γ K) : fconj q (X * Y) = fconj q Y * fconj q X := by
  rw [d_fconj_eq hσ, d_fconj_eq hσ, d_fconj_eq hσ, Matrix.map_mul, Matrix.transpose_mul]
end Formalism.FourierDecayAlt.P.S3x6

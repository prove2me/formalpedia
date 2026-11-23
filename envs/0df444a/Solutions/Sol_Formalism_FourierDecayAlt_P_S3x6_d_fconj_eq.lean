-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.d_fconj_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:29.778447+00:00
-- url     : https://prove2.me/submissions/7bf47d42-dcfe-4cf0-98f6-76e3f34eae66

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
open Matrix Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.S3x6
theorem _root_.solution {q : ℕ} (hσ : ∀ x, σ x = x ^ q) {α β : Type} (X : Matrix α β K) :
    fconj q X = (X.map σ)ᵀ := by
  ext i j
  simp [fconj, hσ]
end Formalism.FourierDecayAlt.P.S3x6

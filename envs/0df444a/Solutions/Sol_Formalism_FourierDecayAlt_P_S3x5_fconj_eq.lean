-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.fconj_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:20.028804+00:00
-- url     : https://prove2.me/submissions/d8d0a4a6-5a08-4cc8-8a16-74af4bf53160

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Matrix Polynomial Formalism.FourierDecayAlt.S3
variable {K : Type} [Field K] [Fintype K]
variable [StarRing K]
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution {q : ℕ} (hs : ∀ x : K, star x = x ^ q) {m n : Type} (X : Matrix m n K) :
    fconj q X = Xᴴ := by
  ext i j
  simp [fconj, hs, Matrix.conjTranspose_apply]
end Formalism.FourierDecayAlt.P.S3x5

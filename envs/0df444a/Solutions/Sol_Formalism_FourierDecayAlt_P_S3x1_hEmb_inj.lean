-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x1.hEmb_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:36:32.328346+00:00
-- url     : https://prove2.me/submissions/4550b199-e187-472a-a9f7-6c69064a6d7a

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_midEmb_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x1
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} {r k : ℕ}
variable [CommRing A]
namespace Formalism.FourierDecayAlt.P.S3x1
theorem _root_.solution {h h' : Matrix (Fin k) (Fin k) A} (e : hEmb r h = hEmb r h') : h = h' := by
  have := congrArg b22 e
  rw [levi_embedding_block22, levi_embedding_block22] at this
  exact midEmb_inj this
end Formalism.FourierDecayAlt.P.S3x1

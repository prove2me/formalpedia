-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.cm_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:19:21.617108+00:00
-- url     : https://prove2.me/submissions/3149b3b4-267a-4436-99ac-7a6063a925c0

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x8
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {A F : Type} [CommRing A] [CommRing F]
namespace Formalism.FourierDecayAlt.P.S3x8
theorem _root_.solution {r : ℕ} (X : Matrix (Fin r) (Fin r) A) (l : ℕ) (hl : l ≤ r) :
    cm (-X) l hl = (-1) ^ l * cm X l hl := by
  unfold cm
  rw [Matrix.submatrix_neg, Pi.neg_apply, Pi.neg_apply, Matrix.det_neg, Fintype.card_fin]
end Formalism.FourierDecayAlt.P.S3x8

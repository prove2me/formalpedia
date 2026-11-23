-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x1.card_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:57.598715+00:00
-- url     : https://prove2.me/submissions/b06f0e33-1920-44eb-9a8e-ecff22dad245

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective

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
namespace Formalism.FourierDecayAlt.P.S3x1
theorem _root_.solution (m n K : Type) [Finite m] [Finite n] :
    Nat.card (Matrix m n K) = Nat.card K ^ (Nat.card m * Nat.card n) := by
  show Nat.card (m → n → K) = _
  rw [Nat.card_fun, Nat.card_fun, ← pow_mul, mul_comm]
end Formalism.FourierDecayAlt.P.S3x1

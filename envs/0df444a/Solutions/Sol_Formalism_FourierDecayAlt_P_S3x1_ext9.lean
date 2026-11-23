-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x1.ext9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:57.695801+00:00
-- url     : https://prove2.me/submissions/c5260ef7-47cf-4598-81b4-05c338b494e3

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
variable {A : Type} {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x1
theorem _root_.solution {x y : Matrix (Idx r k) (Idx r k) A} (h11 : b11 x = b11 y) (h12 : b12 x = b12 y)
    (h13 : b13 x = b13 y) (h21 : b21 x = b21 y) (h22 : b22 x = b22 y) (h23 : b23 x = b23 y)
    (h31 : b31 x = b31 y) (h32 : b32 x = b32 y) (h33 : b33 x = b33 y) : x = y := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j
  · exact congrFun (congrFun h11 i) j
  · exact congrFun (congrFun h12 i) j
  · exact congrFun (congrFun h13 i) j
  · exact congrFun (congrFun h21 i) j
  · exact congrFun (congrFun h22 i) j
  · exact congrFun (congrFun h23 i) j
  · exact congrFun (congrFun h31 i) j
  · exact congrFun (congrFun h32 i) j
  · exact congrFun (congrFun h33 i) j
end Formalism.FourierDecayAlt.P.S3x1

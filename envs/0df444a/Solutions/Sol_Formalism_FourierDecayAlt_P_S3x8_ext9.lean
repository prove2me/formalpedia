-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.ext9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:11:46.304936+00:00
-- url     : https://prove2.me/submissions/3739c9fa-8f6d-4687-93d5-c088ab3ee03a

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
variable {A : Type} {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x8
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
end Formalism.FourierDecayAlt.P.S3x8

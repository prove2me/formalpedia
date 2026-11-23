-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x9.block32_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:47.993163+00:00
-- url     : https://prove2.me/submissions/0199a41d-dc15-48c3-a93a-82ae130dbc14

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Minors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block32EqZeroOfUnipotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x9
open Matrix Finset
open Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni upUniG)
namespace Formalism.FourierDecayAlt.P.S3x9
theorem _root_.solution {A B : Type} {r k : ℕ} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b32 (x.map f) = (b32 x).map f := rfl
end Formalism.FourierDecayAlt.P.S3x9

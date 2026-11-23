-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x3.card_NU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:11.713869+00:00
-- url     : https://prove2.me/submissions/faefe786-dd3f-4539-8257-0596fdfed188

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_card_prod_set
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_isUnit_det_of_isUpUni

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x3
open Matrix Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni upUniG)
variable {A : Type} [CommRing A] {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x3
theorem _root_.solution : Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsNU x} =
    Nat.card (upUniG A k) * Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsN x} :=
  card_prod_set (r := r) (fun h : Matrix (Fin k) (Fin k) A => IsUpUni h)
    (fun _ h => isUnit_det_of_isUpUni h)
end Formalism.FourierDecayAlt.P.S3x3

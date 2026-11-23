-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x3.index_JH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:12.127006+00:00
-- url     : https://prove2.me/submissions/a33b7e86-34c1-4eaa-84f7-ec0e8e979118

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_red_surjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_index_mul_card

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
variable (o : Type) [CommRing o] [IsLocalRing o] {r k : ℕ} (L : Levels o r k)
namespace Formalism.FourierDecayAlt.P.S3x3
theorem _root_.solution : L.JH.index * Nat.card (upUniG (IsLocalRing.ResidueField o) k) =
    Nat.card (GL (Fin k) (IsLocalRing.ResidueField o)) :=
  index_mul_card (red o (Fin k)) (red_surjective o _) L.JH _ L.mem_JH
end Formalism.FourierDecayAlt.P.S3x3

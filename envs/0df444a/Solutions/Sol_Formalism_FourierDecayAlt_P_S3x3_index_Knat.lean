-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x3.index_Knat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:27.321433+00:00
-- url     : https://prove2.me/submissions/4a42f4f5-3e2e-4aa2-ae35-6e24a474f648

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_red_surjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_index_mul_card
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_card_GL_subtype
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_isUnit_det_of_isS
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_card_S

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
theorem _root_.solution : L.Knat.index *
    (Nat.card (GL (Fin k) (IsLocalRing.ResidueField o)) *
      Nat.card {x : Matrix (Idx r k) (Idx r k) (IsLocalRing.ResidueField o) // IsN x}) =
    Nat.card (GL (Idx r k) (IsLocalRing.ResidueField o)) := by
  rw [← card_S, ← card_GL_subtype _ (fun _ h => isUnit_det_of_isS h)]
  exact index_mul_card (red o (Idx r k)) (red_surjective o _) L.Knat _ L.mem_Knat
end Formalism.FourierDecayAlt.P.S3x3

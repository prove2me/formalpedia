-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.zj_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:34:56.252374+00:00
-- url     : https://prove2.me/submissions/9fb97657-6d03-41e1-9a5a-b163a7ee56ac

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_block2_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux5
namespace Formalism.FourierDecayAlt.P.Ux5
theorem _root_.solution {p s : ℕ} (a : Fin s → Fin p → ℂ) (b : Fin p → Fin s → ℂ) (H : Matrix (Fin p) (Fin p) ℂ)
    (CC : Matrix (Fin s) (Fin s) ℂ) :
    Zj a b H CC = blk2 H (H * Matrix.of b) (Matrix.of a * H) (Matrix.of a * H * Matrix.of b + CC) := by
  unfold Zj
  rw [block2_mul, block2_mul]
  simp
end Formalism.FourierDecayAlt.P.Ux5

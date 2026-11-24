-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.block2_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:34:07.748811+00:00
-- url     : https://prove2.me/submissions/5b49cf15-5ee1-447d-be8e-9f957fa54c43

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks

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
theorem _root_.solution {p s : ℕ} : blk2 (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (1 : Matrix (Fin s) (Fin s) ℂ) = 1 := by
  unfold blk2
  rw [fromBlocks_one, reindex_apply, submatrix_one_equiv]
end Formalism.FourierDecayAlt.P.Ux5

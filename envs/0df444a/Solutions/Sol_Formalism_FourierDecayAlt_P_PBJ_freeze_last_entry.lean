-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBJ.freeze_last_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:02:51.411345+00:00
-- url     : https://prove2.me/submissions/cfed3bb3-3b4f-4ea3-aaf0-4ed9ea259a6b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KloostDensOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockTwoDiagonalZeroSize
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_phiTop_freeze
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_kcls_Psc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBJ
namespace Formalism.FourierDecayAlt.P.PBJ
theorem _root_.solution : FreezeLast := by
  intro β p V _ _ _ Ψ hΨ c hc
  refine ⟨Frz.Psc β c Ψ, Frz.kcls_Psc β c hΨ hc, fun σ d hd => ?_⟩
  exact Frz.phiTop_freeze β c σ d hd hΨ
end Formalism.FourierDecayAlt.P.PBJ

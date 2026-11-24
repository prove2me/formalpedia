-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBJ.Frz.isCompact_Sset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:12:53.028969+00:00
-- url     : https://prove2.me/submissions/0ae5dd89-81cf-46ca-9685-ff2fc22000b1

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KloostDensOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockTwoDiagonalZeroSize
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_cont_detM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBJ Formalism.FourierDecayAlt.P.PBJ.Frz
open MeasureTheory Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace Formalism.FourierDecayAlt.P.PBJ.Frz
theorem _root_.solution (p : ℕ) (R δ' : ℝ) : IsCompact (Sset p R δ') := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact (isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const (continuous_norm.comp (cont_detM p)))
  · exact (Metric.isBounded_closedBall (x := (0 : G.Mat p)) (r := R)).subset fun H hH => by
      simpa [Metric.mem_closedBall, dist_zero_right] using hH.1
end Formalism.FourierDecayAlt.P.PBJ.Frz

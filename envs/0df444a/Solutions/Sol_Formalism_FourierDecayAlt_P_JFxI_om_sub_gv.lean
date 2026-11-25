-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxI.om_sub_gv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:54:19.876048+00:00
-- url     : https://prove2.me/submissions/4ed9662c-b699-431f-ad48-7cce95cbd680

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfBetaAdjCOfLemmaBNorm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDiagonalMap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellInversePair
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordIntegralScaling
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothWordsAll
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliUnderIntegral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfExhaustOfAvgCutoff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxI
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.JFxI
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) : Om k r z z' ⊆ GV k r := by
  exact Set.inter_subset_left
end Formalism.FourierDecayAlt.P.JFxI

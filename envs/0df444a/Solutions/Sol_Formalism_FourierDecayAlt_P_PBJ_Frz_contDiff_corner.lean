-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBJ.Frz.contDiff_corner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:09:42.680607+00:00
-- url     : https://prove2.me/submissions/922f61c1-1569-4fb9-98a5-152f9deb2ea3

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KloostDensOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockTwoDiagonalZeroSize

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
theorem _root_.solution (p : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : G.Mat p × AB p => cornerA q.2.1 + cornerB q.2.2) := by
  by_cases hp : 0 < p
  · have e : (fun q : G.Mat p × AB p => cornerA q.2.1 + cornerB q.2.2) =
        fun q => q.2.1 0 ⟨p - 1, by omega⟩ + q.2.2 ⟨p - 1, by omega⟩ 0 := by
      funext q; simp [cornerA, cornerB, hp]
    rw [e]; fun_prop
  · have e : (fun q : G.Mat p × AB p => cornerA q.2.1 + cornerB q.2.2) = fun _ => 0 := by
      funext q; simp [cornerA, cornerB, hp]
    rw [e]; exact contDiff_const
end Formalism.FourierDecayAlt.P.PBJ.Frz

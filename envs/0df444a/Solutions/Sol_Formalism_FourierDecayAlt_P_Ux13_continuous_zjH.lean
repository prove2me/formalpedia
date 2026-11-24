-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux13.continuous_zjH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:46:32.035947+00:00
-- url     : https://prove2.me/submissions/2063f33d-6b35-4d24-96f6-a7c94e76f556

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux13_continuous_block2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux13_continuous_lowW
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux13_continuous_upper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux13
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
namespace Formalism.FourierDecayAlt.P.Ux13
theorem _root_.solution {p s : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (CC : G.Mat s) :
    Continuous fun η : XiH p s σ => (Matrix.of.symm (ZjH σ d η CC) : G.Mat (p + s)) := by
  have hof1 : Continuous fun η : XiH p s σ => (Matrix.of η.1.1 : Matrix (Fin s) (Fin p) ℂ) :=
    continuous_matrix fun i j => (continuous_apply_apply i j).comp (continuous_fst.comp continuous_fst)
  have hof2 : Continuous fun η : XiH p s σ => (Matrix.of η.1.2 : Matrix (Fin p) (Fin s) ℂ) :=
    continuous_matrix fun i j => (continuous_apply_apply i j).comp (continuous_snd.comp continuous_fst)
  have hH : Continuous fun η : XiH p s σ => headH σ d η.2.1 η.2.2 := by
    unfold headH
    exact ((continuous_const.matrix_mul ((continuous_lowW σ).comp (continuous_fst.comp continuous_snd))).matrix_mul
      continuous_const).matrix_mul (continuous_upper.comp (continuous_snd.comp continuous_snd))
  have hZ : Continuous fun η : XiH p s σ => ZjH σ d η CC := by
    unfold ZjH Zj
    exact ((continuous_block2 continuous_const continuous_const hof1 continuous_const).matrix_mul
      (continuous_block2 hH continuous_const continuous_const continuous_const)).matrix_mul
      (continuous_block2 continuous_const hof2 continuous_const continuous_const)
  exact hZ
end Formalism.FourierDecayAlt.P.Ux13

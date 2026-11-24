-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBJ.Frz.block_two_one_upper_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:54:55.178915+00:00
-- url     : https://prove2.me/submissions/a695dfcd-8db5-4f0b-bc58-2bda821a4599

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
theorem _root_.solution {p : ℕ} (b : Fin p → Fin 0 → ℂ) :
    (blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (Matrix.of b) 0 1 : Matrix (Fin (p + 0)) (Fin (p + 0)) ℂ) = 1 := by
  ext i j
  obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
  rcases i' with i' | i'
  · rcases j' with j' | j'
    · simp [blk2, Matrix.one_apply]
    · exact j'.elim0
  · exact i'.elim0
end Formalism.FourierDecayAlt.P.PBJ.Frz

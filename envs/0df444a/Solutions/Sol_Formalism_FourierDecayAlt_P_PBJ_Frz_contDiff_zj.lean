-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBJ.Frz.contDiff_zj
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:57:35.966093+00:00
-- url     : https://prove2.me/submissions/d892f5d1-e33b-4d77-84c1-f4b531f2ef67
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KloostDensOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockTwoDiagonalZeroSize
import Theorems.Thm_Formalism_FourierDecayAlt_P_level_z_affine


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
theorem _root_.solution (p : ℕ) (C : Matrix (Fin 1) (Fin 1) ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : G.Mat p × AB p =>
      fun (i j : Fin (p + 1)) => Zj q.2.1 q.2.2 (Matrix.of q.1) C i j) := by
  have e : (fun q : G.Mat p × AB p => fun (i j : Fin (p + 1)) => Zj q.2.1 q.2.2 (Matrix.of q.1) C i j) = fun q =>
      fun (i j : Fin (p + 1)) => blk2 (Matrix.of q.1) (Matrix.of q.1 * Matrix.of q.2.2) (Matrix.of q.2.1 * Matrix.of q.1)
        (Matrix.of q.2.1 * Matrix.of q.1 * Matrix.of q.2.2 + C) i j := by
    funext q; rw [Formalism.FourierDecayAlt.P.level_z_affine]
  rw [e]
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
  rcases i' with i' | i' <;> rcases j' with j' | j' <;>
    simp only [blk2, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.mul_apply,
      Matrix.add_apply, Matrix.of_apply] <;> fun_prop
end Formalism.FourierDecayAlt.P.PBJ.Frz

-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux13.zjH_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:31:04.561266+00:00
-- url     : https://prove2.me/submissions/ac666445-3768-4676-953f-735694f6f51c

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts

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
theorem _root_.solution (hZ : ZjAffine) {p s : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (η : XiH p s σ)
    (CC : G.Mat s) :
    (Matrix.of.symm (ZjH σ d η CC) : G.Mat (p + s)) = Matrix.of.symm (ZjH σ d η 0) + iotaL p s CC := by
  have h : ∀ (H : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ) (C : Matrix (Fin s) (Fin p) ℂ)
      (D Z : Matrix (Fin s) (Fin s) ℂ), blk2 H B C (D + Z) = blk2 H B C (D + 0) + blk2 0 0 0 Z := by
    intro H B C D Z
    rw [block2_add]
    simp
  unfold ZjH
  rw [hZ, hZ, h _ _ _ _ (Matrix.of CC)]
  rfl
end Formalism.FourierDecayAlt.P.Ux13

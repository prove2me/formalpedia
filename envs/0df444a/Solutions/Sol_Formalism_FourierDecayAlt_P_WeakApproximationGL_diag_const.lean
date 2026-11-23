-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakApproximationGL.diag_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:36:47.960926+00:00
-- url     : https://prove2.me/submissions/daf9a5de-1210-48f6-bc02-2ee1ed4a34d8

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WeakApproximationGL
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G5
namespace Formalism.FourierDecayAlt.P.WeakApproximationGL
theorem _root_.solution (m : ℕ) (z : ℂ) :
    Matrix.diagonal (Fin.cons z (fun _ : Fin (m + 1) => z) : Fin (m + 2) → ℂ) =
      z • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) := by
  have hc : (Fin.cons z (fun _ : Fin (m + 1) => z) : Fin (m + 2) → ℂ) = fun _ => z := by
    funext i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩ <;> simp
  rw [hc, Matrix.smul_one_eq_diagonal]
end Formalism.FourierDecayAlt.P.WeakApproximationGL

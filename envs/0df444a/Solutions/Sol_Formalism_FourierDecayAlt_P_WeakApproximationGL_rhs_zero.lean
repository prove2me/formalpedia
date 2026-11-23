-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakApproximationGL.rhs_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:12.75645+00:00
-- url     : https://prove2.me/submissions/066fff74-a571-4d2f-b92c-8a4a2ece5e13

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
theorem _root_.solution {m : ℕ} (t ρ₁ : ℂ) (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ) {j : Fin (m + 2)} (h : 0 < j) :
    (t • subShift (m + 2) + Matrix.diagonal (Fin.cons ρ₁ x : Fin (m + 2) → ℂ) + strictUpper y) 0 j =
      triXY x y 0 j := by
  simp [triXY, subShift, Matrix.diagonal_apply_ne _ h.ne]
end Formalism.FourierDecayAlt.P.WeakApproximationGL

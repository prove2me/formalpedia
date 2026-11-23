-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakApproximationGL.tri_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:06.874037+00:00
-- url     : https://prove2.me/submissions/a4f3a774-6ce0-421f-9c68-440195a8a8b8

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
theorem _root_.solution {m : ℕ} (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ) {i j : Fin (m + 2)} (h : i < j) :
    triXY x y i j = y ⟨(i, j), h⟩ := by
  simp [triXY, strictUpper, h, Matrix.diagonal_apply_ne _ h.ne]
end Formalism.FourierDecayAlt.P.WeakApproximationGL

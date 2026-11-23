-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakApproximationGL.tri_gt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:24.154157+00:00
-- url     : https://prove2.me/submissions/5239e270-8b4f-44b3-b3bd-52619aaba506

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
theorem _root_.solution {m : ℕ} (x : Fin (m + 1) → ℂ) (y : UT (m + 2) → ℂ) {i j : Fin (m + 2)} (h : j < i) :
    triXY x y i j = 0 := by
  simp [triXY, strictUpper, not_lt.mpr h.le, Matrix.diagonal_apply_ne _ h.ne']
end Formalism.FourierDecayAlt.P.WeakApproximationGL

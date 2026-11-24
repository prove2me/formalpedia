-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakApproximationGL.strictUpper_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:53.2628+00:00
-- url     : https://prove2.me/submissions/befd9545-ac59-4c8f-89f2-f72994aa7124

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
theorem _root_.solution {d : ℕ} {y y' : UT d → ℂ} {a b : Fin d → ℂ}
    (h : Matrix.diagonal a + strictUpper y = Matrix.diagonal b + strictUpper y') : y = y' := by
  funext q
  obtain ⟨⟨i, j⟩, hij⟩ := q
  have h' := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i j) h
  simpa [strictUpper, hij, Matrix.diagonal_apply_ne _ hij.ne] using h'
end Formalism.FourierDecayAlt.P.WeakApproximationGL

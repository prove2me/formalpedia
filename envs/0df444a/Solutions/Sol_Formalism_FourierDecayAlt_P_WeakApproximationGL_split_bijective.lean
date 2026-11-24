-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakApproximationGL.split_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:52.656254+00:00
-- url     : https://prove2.me/submissions/a12aab77-c035-455e-aa02-a80bc47529a2

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
theorem _root_.solution (m : ℕ) : Function.Bijective (split m) := by
  refine ⟨fun v w h => ?_, fun q => ⟨Sum.elim (fun _ => q.1) (Sum.elim q.2.1 (Sum.elim q.2.2.1 q.2.2.2)), rfl⟩⟩
  simp only [split, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  funext s
  rcases s with ⟨⟩ | k | q | i
  · exact h1
  · exact congrFun h2 k
  · exact congrFun h3 q
  · exact congrFun h4 i
end Formalism.FourierDecayAlt.P.WeakApproximationGL

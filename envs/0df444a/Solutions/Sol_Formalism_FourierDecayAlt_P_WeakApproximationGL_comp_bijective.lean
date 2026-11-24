-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakApproximationGL.comp_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:49.544577+00:00
-- url     : https://prove2.me/submissions/a29b7fa9-f3b5-43e6-93e6-e267260edb4e

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
theorem _root_.solution (m : ℕ) : Function.Bijective (fun v : FinalTheorems m → ℂ => v ∘ idx m) := by
  refine ⟨fun v w h => funext fun s => ?_, fun u => ⟨u ∘ (idxE m).symm, funext fun t => ?_⟩⟩
  · obtain ⟨t, rfl⟩ := idx_surjective m s
    exact congrFun h t
  · simp only [Function.comp_apply]
    congr 1
    exact (idxE m).symm_apply_apply t
end Formalism.FourierDecayAlt.P.WeakApproximationGL

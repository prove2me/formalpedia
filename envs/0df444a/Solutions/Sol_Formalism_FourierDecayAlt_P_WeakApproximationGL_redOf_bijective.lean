-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakApproximationGL.redOf_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:24.216061+00:00
-- url     : https://prove2.me/submissions/99c42da0-8005-499f-b72d-e92411a1763b

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_redOf_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_split_bijective
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_elim_bijective
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_comp_bijective

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
theorem _root_.solution (m : ℕ) : Function.Bijective (redOf m) := by
  have h : redOf m = split m ∘ (fun v : FinalTheorems m → ℂ => v ∘ idx m) ∘
      (fun p : XY m => (Sum.elim p.1 p.2 : FinalTheorems m → ℂ)) := funext (redOf_eq m)
  rw [h]
  exact (split_bijective m).comp ((comp_bijective m).comp (elim_bijective m))
end Formalism.FourierDecayAlt.P.WeakApproximationGL

-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.split_xy_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:16.282509+00:00
-- url     : https://prove2.me/submissions/3dad251a-4276-409a-8846-e9fa111d34a1

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_redOf_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_redOf_bijective
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_mp_elim
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakApproximationGL_mp_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_mp_comp_equiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.WeakApproximationGL
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.SplitXY := by
  intro m β
  refine ⟨redOf_bijective m, ?_⟩
  have h : redOf m = split m ∘ (fun v : FinalTheorems m → ℂ => v ∘ idx m) ∘
      (fun p : XY m => (Sum.elim p.1 p.2 : FinalTheorems m → ℂ)) := funext (redOf_eq m)
  rw [h]
  exact (mp_split β m).comp ((Formalism.FourierDecayAlt.P.G5.mp_comp_equiv β (idxE m)).comp (mp_elim β m))
end Formalism.FourierDecayAlt.P

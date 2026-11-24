-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lower_splitting_measurable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:52:21.850838+00:00
-- url     : https://prove2.me/submissions/36fd6537-4453-4585-9410-e526e7543e6a

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShearMeasurability
import Theorems.Thm_Formalism_FourierDecayAlt_P_ShearMeasurability_shear_mp
import Theorems.Thm_Formalism_FourierDecayAlt_P_ShearMeasurability_eSplit_mp
import Theorems.Thm_Formalism_FourierDecayAlt_P_ShearMeasurability_shear_cond
import Theorems.Thm_Formalism_FourierDecayAlt_P_ShearMeasurability_shear_meas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open ShearMeasurability
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.LowSplitMeas := by
  intro m w
  have h1 := shear_mp gap (fun x => mulMap w (eSplit w x)) (shear_meas w) (shear_cond w)
  have h2 := (eSplit_mp w).symm (eSplit w)
  have h3 := h1.comp h2
  convert h3 using 1
  all_goals try rfl
  funext p
  simp only [Function.comp, MeasurableEquiv.apply_symm_apply]
  rfl
end Formalism.FourierDecayAlt.P

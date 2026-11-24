-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.model_is_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:45:19.321906+00:00
-- url     : https://prove2.me/submissions/f0f78d42-d8fd-4008-8588-6e40fd589622

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModelLevelMultiplier
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx1_model_level_multiplier
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx1_model_level_lowering

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Q.ModelIsNF := by
  intro P L hL Y
  have hm := Qx1.model_level_multiplier P L hL Y
  have hl := Qx1.model_level_lowering P L hL Y
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGG, hGGi, -, -, -⟩ := hL
  simp only [NFData.QQ, hm, hl, hGG, hGGi]
  rfl
end Formalism.FourierDecayAlt.P

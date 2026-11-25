-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.jDOpR_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:40:31.270082+00:00
-- url     : https://prove2.me/submissions/5f0a3d03-a408-4455-9114-5bfa0625f4c9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatOpA
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_hatOK_of_poly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP
open NumberField
noncomputable section
namespace Formalism.FourierDecayAlt.P.CutMP
theorem _root_.solution (hP : JDPolyOK) (hC : JDCapR) : JDOpR := by
  refine ⟨1, zero_le_one, ?_⟩
  intro Cc hCc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hQQ hL y
  obtain ⟨Θ, Θv, hΘ, hΘv, hc, hcv, h⟩ := hC Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hQQ hL y
  exact ⟨Θ, Θv, hatOK_of_poly hP hCc hΘ hc, hatOK_of_poly hP hCc hΘv hcv, h⟩
end Formalism.FourierDecayAlt.P.CutMP

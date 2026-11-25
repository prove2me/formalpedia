-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.jDOpA_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:31:55.101466+00:00
-- url     : https://prove2.me/submissions/58822fc2-6da4-4075-a51a-0dfd8a2d54d0

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
theorem _root_.solution (hP : JDPolyOK) (hC : JDCapA) : JDOpA := by
  refine ⟨1, zero_le_one, ?_⟩
  intro Cc hCc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hL y
  obtain ⟨Θ, Θv, hΘ, hΘv, hc, hcv, h⟩ := hC Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hL y
  exact ⟨Θ, Θv, hatOK_of_poly hP hCc hΘ hc, hatOK_of_poly hP hCc hΘv hcv, h⟩
end Formalism.FourierDecayAlt.P.CutMP

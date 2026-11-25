-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.compactly_supported_banach_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:57:10.255798+00:00
-- url     : https://prove2.me/submissions/bcb93fef-6bf0-4d52-adcb-42a90f0d5b8a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_vs_closed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.U.CCModelExists := by
  intro k ρ E _ _ _ a mm S
  have : IsClosed (Ux1.Vs E a mm S : Set (Ux1.Lp k ρ mm E)) := Ux1.vs_closed a mm S
  exact ⟨Ux1.Vs E a mm S, inferInstance, inferInstance, IsClosed.completeSpace_coe,
    ⟨Ux1.model a mm S⟩⟩
end Formalism.FourierDecayAlt.P

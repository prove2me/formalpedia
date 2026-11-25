-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.onLocal_of_onLocalJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:38:23.147285+00:00
-- url     : https://prove2.me/submissions/d46a3d40-76b9-4c56-a290-5480195e154d

import Definitions.Def_Formalism_MirabolicMackeyTheory_LocalConditionsWeighted
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (h : OnLocalJ) : OnLocal := by
  exact fun K _ _ _ Z _ _ _ _ _ w P _ _ ρ U ψ hMk V₀ e he hr M Th ThK Th0 X₃ X₄ hM hTh hThK hle hFG hEig hMs hTs
    σ hσ hsc hdata a E r ha hE hT0 h0 h3 h4 h34 ε hTW =>
    h K Z w P ρ U ψ hMk V₀ e he hr M Th ThK Th0 Th0 X₃ X₄ hM hTh hThK hle hFG hEig hMs hTs
      σ hσ hsc hdata a E r ha hE hT0 h0 h0 le_rfl h3 h4 h34 ε hTW
end Formalism.EigenvalueLevelCeiling

-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.local_conditions_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:54:59.127345+00:00
-- url     : https://prove2.me/submissions/6f3ecf30-02c8-48ae-81ed-970f86d6b302

import Definitions.Def_Formalism_MirabolicMackeyTheory_LocalConditionsWeighted
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_twist_chain
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxCutLe
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_onLocal


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
theorem _root_.solution : OnLocalJ := by
  intro K _ _ _ Z _ _ _ _ _ w P _ _ ρ U ψ hMk V₀ e he hr M Th ThK Th0 ThJ X₃ X₄ hM hTh hThK hle hFG hEig hMs hTs
    σ hσ hsc hdata a E r ha hE hT0 h0 hJ h0J h3 h4 h34 ε hTW d φ hinj hrng Mj Tj hMj hTj
  exact onLocal K Z w P ρ U ψ hMk V₀ e he hr M Th ThK Th0 X₃ X₄ hM hTh hThK hle hFG hEig hMs hTs σ hσ hsc hdata
    a E r ha hE hT0 h0 h3 h4 h34 ε
    (twist_chain K Z w _ e _ Th0 ThJ X₃ (idxCutLe K Z w ⊤ _ M Th hM hTh hle le_top).1 h0 hJ h0J ε hTW)
    d φ hinj hrng Mj Tj hMj hTj
end Formalism.EigenvalueLevelCeiling

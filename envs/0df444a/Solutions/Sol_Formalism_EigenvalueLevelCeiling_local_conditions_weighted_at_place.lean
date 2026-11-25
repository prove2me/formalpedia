-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.local_conditions_weighted_at_place
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:25:28.651353+00:00
-- url     : https://prove2.me/submissions/46dadfc6-7fd2-4ccd-940f-20a0fd4b794d

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementLoc
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsWeightedConditional
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_locP
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_inf_lat
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_local_conditions_weighted


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
open Formalism.DivisionValues Formalism.HermitianLatticesTheory
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : LocalConditionsWeightedAtPlace := by
  intro K _ _ _ Z _ _ _ _ _ w P _ _ ρ U ψ hMk V₀ e he hr M Th1 Th ThK Th0 ThJ X₃ hM hTh1 hTh hThK h1le hle hFG hEig
    hMs hTs σ hσ hsc hdata a E r ha hE hT0 h0 hJ h0J h3 X _ _ _ _ θ' eX pr Mt hc hpr h4 h34 ε hTW d φ hinj hrng
    Mj Tj hMj hTj
  exact local_conditions_weighted K Z w P ρ U ψ hMk V₀ e he hr M Th1 Th ThK Th0 ThJ
    (X₃ ⊓ (Mt.map (θ'.restrictScalars (𝓞 K))).map (e.restrictScalars (𝓞 K)))
    hM hTh1 hTh hThK h1le hle hFG hEig hMs hTs σ hσ hsc hdata a E r ha hE hT0 h0 hJ h0J
    (idxRules_inf_lat h3 h4) X θ' eX pr Mt hc hpr h4 inf_le_right ε
    (by rw [locP w _ _ _ h34]; exact hTW) d φ hinj hrng Mj Tj hMj hTj
end Formalism.EigenvalueLevelCeiling

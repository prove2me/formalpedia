-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.log_unique_bis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:18:45.907553+00:00
-- url     : https://prove2.me/submissions/37fa7470-52f9-46dd-a45c-8497a8127203

import Definitions.Def_Formalism_FrobeniusBaseCase_StatementFix
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseFalseGeneralHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_FixAll
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_LogIffFix_statement
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_hasUniqueFixedPoint


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical
open Formalism.BaseCaseIdentities.Data
variable {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C] (D : Data k Z C)
namespace Formalism.BaseCaseIdentities.Data
theorem _root_.solution : D.LogUnique := by
  obtain ⟨t, ⟨h0, h1⟩, huniq⟩ := D.hasUniqueFixedPoint.1
  exact ⟨t, ⟨h0, (D.LogIffFix_statement t h0).2 h1⟩,
    fun t' ht' => huniq t' ⟨ht'.1, (D.LogIffFix_statement t' ht'.1).1 ht'.2⟩⟩
end Formalism.BaseCaseIdentities.Data

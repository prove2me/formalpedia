-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.index_scale_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:18:53.851499+00:00
-- url     : https://prove2.me/submissions/cc85e649-4b74-4671-adc1-c72c6a89a4db

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_add
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_scG_lat
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_scale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues Formalism.HermitianLatticesTheory
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : IdxScaleIn := by
  intro K _ _ _ Z _ _ _ _ _ w W A B hA hB a ha
  have hl := idxRules_scG_lat (R := 𝓞 K) ha hB
  refine ⟨hl, ?_⟩
  have h := idxRules_add w.asIdeal W A B (scG a B) hA hB hl
  have h2 := idxRules_scale w W B hB ha
  change lidx w.asIdeal A (scG a B) = lidx w.asIdeal A B + _
  rw [h, h2]
  rfl
end Formalism.EigenvalueLevelCeiling

-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.index_truncation_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:04.597711+00:00
-- url     : https://prove2.me/submissions/977e615c-f1c8-456e-846c-28de83f6a33a

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_fin
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_le_locS
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_lidx_of_le
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_cut_lat
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_cut_le

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
theorem _root_.solution : IdxCutLe := by
  intro K _ _ _ Z _ _ _ _ _ w W W' A B hA hB hle hW
  have hcl : cut W' B ≤ cut W' A := inf_le_inf_right _ hle
  have h1 : lix w (cut W' A) (cut W' B) = locLen w.asIdeal (cut W' A) (cut W' B) :=
    idxRules_lidx_of_le _ hcl
  have h2 : lix w A B = locLen w.asIdeal A B := idxRules_lidx_of_le _ hle
  refine ⟨idxRules_cut_lat hW hA, ?_, ?_⟩
  · rw [h1]
    exact Int.natCast_nonneg _
  · rw [h1, h2]
    exact_mod_cast idxRules_cut_le w.asIdeal W' A B
      (idxRules_fin w.asIdeal A B hA.1 (idxRules_le_locS hA.2 hB.2))
end Formalism.EigenvalueLevelCeiling

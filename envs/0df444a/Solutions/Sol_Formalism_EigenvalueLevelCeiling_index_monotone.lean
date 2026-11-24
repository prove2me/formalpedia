-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.index_monotone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:42:30.41931+00:00
-- url     : https://prove2.me/submissions/0fc6ed99-691b-4938-b43d-9bc335e17f91

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_add
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_lidx_of_le

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
theorem _root_.solution : IdxMono := by
  intro K _ _ _ Z _ _ _ _ _ w W A B B' hA hB hB' hle
  have h := idxRules_add w.asIdeal W A B' B hA hB' hB
  have h2 : lidx w.asIdeal B' B = locLen w.asIdeal B' B := idxRules_lidx_of_le _ hle
  unfold lix
  rw [h, h2]
  have : (0 : ℤ) ≤ (locLen w.asIdeal B' B : ℤ) := Int.natCast_nonneg _
  linarith
end Formalism.EigenvalueLevelCeiling

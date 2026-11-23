-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.lattice_intersection
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:20.736283+00:00
-- url     : https://prove2.me/submissions/0c5fceb7-4fa1-416e-b72d-35111af598a9

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_scG_lat
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_inf_lat

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
theorem _root_.solution : LatInter := by
  intro K _ _ _ Z _ _ _ _ _ A B hA hB a ha
  exact idxRules_inf_lat hA (idxRules_scG_lat (R := 𝓞 K) ha hB)
end Formalism.EigenvalueLevelCeiling

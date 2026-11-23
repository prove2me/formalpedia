-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.local_conditions_global_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:51.880123+00:00
-- url     : https://prove2.me/submissions/52617807-5d77-4954-85ec-8958c011257e

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_onExport2_of
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ramified_basic_bound


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
theorem _root_.solution : OnExport2 := onExport2_of ramified_basic_bound
end Formalism.EigenvalueLevelCeiling

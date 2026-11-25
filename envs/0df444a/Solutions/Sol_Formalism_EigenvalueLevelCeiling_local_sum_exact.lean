-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.local_sum_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:03:08.534006+00:00
-- url     : https://prove2.me/submissions/6ad5f35d-791f-4108-9982-2afe0b9d65b0

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_ErrSumGoodExact
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsComposeGeneral
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PrimeLogOverP
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PrimeLogOverPSqTail
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditionsOfExact
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_error_sum_good_places_exact
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_onSumExact_of
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_place_sum
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
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : OnSumExact := onSumExact_of place_sum ramified_basic_bound error_sum_good_places_exact
end Formalism.EigenvalueLevelCeiling

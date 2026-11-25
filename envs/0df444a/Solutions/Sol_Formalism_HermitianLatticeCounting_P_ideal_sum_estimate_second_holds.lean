-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.ideal_sum_estimate_second_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:00:55.994504+00:00
-- url     : https://prove2.me/submissions/68c748af-667e-41ed-86cd-4827669f03df

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_ideal_norm_product_lower_bound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_ideal_inverse_power_sum_of_norm_separated
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_separated_sum_estimate_second_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.IdealInversePowerSum := ideal_inverse_power_sum_of_norm_separated ideal_norm_product_lower_bound separated_sum_estimate_second_holds
end Formalism.HermitianLatticeCounting.P

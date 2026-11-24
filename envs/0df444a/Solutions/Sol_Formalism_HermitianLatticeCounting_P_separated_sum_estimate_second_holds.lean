-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.separated_sum_estimate_second_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:24.036423+00:00
-- url     : https://prove2.me/submissions/737b6dfc-a160-4b2b-91c2-bc529594c219

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_disjointness_of_supports_holds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_inverse_power_integral_pi
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_separated_set_sum_bound_of_disjoint_integral

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
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.SeparatedSetSumBound := separated_set_sum_bound_of_disjoint_integral disjointness_of_supports_holds inverse_power_integral_pi
end Formalism.HermitianLatticeCounting.P

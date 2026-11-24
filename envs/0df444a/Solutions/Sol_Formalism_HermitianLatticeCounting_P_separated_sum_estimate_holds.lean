-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.separated_sum_estimate_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:25.369915+00:00
-- url     : https://prove2.me/submissions/7715eead-a735-45a4-a3b8-d770c7171650

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_disjointness_of_supports_holds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_cutoff_integral_formula
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_separated_cutoff_sum_of_disjoint_polydiscs

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
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.SeparatedCutoffSum := separated_cutoff_sum_of_disjoint_polydiscs disjointness_of_supports_holds cutoff_integral_formula
end Formalism.HermitianLatticeCounting.P

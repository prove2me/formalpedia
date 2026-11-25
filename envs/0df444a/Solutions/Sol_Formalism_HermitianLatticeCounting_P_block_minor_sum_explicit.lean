-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.block_minor_sum_explicit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:08:32.237082+00:00
-- url     : https://prove2.me/submissions/0ad054e2-ac11-417d-8d75-26be231b570e

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_composition_block_prod_bound
import Theorems.Thm_P2M_Formalism_HermitianLatticeCounting_P_block_end_minor_fibre_finite__f8185a474196
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_block_minor_sum_explicit_of_fibre_finite_of_prod_bound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_ideal_sum_estimate_second_holds

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
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.BlockMinorSumExplicit := block_minor_sum_explicit_of_fibre_finite_of_prod_bound block_end_minor_fibre_finite' composition_block_prod_bound ideal_sum_estimate_second_holds
end Formalism.HermitianLatticeCounting.P

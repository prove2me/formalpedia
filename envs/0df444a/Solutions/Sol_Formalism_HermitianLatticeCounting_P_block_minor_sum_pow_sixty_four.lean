-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.block_minor_sum_pow_sixty_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:19:36.948489+00:00
-- url     : https://prove2.me/submissions/652629ca-60ab-49b2-bd57-8cc2419dd3e6

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_blockMinorSumPowSixtyFour_of_blockMinorSumExplicit
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_block_minor_sum_explicit

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
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.BlockMinorSumPowSixtyFour := blockMinorSumPowSixtyFour_of_blockMinorSumExplicit block_minor_sum_explicit
end Formalism.HermitianLatticeCounting.P

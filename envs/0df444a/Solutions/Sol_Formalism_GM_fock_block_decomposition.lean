-- Prove2me | solution 1 for Formalism.GM.fock_block_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:45:40.267799+00:00
-- url     : https://prove2.me/submissions/f3ea586a-a604-42b2-9b81-509ac150f77e

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_fock_blocks_of_weights

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
namespace Formalism.GM
theorem _root_.solution : M.FockBlocks := FockB.fock_blocks_of_weights
end Formalism.GM

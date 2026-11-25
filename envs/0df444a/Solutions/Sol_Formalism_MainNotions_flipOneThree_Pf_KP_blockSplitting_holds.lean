-- Prove2me | solution 1 for Formalism.MainNotions.flipOneThree.Pf.KP.blockSplitting_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:18:32.295697+00:00
-- url     : https://prove2.me/submissions/3dc1b7f7-e4e6-4bfc-8e04-1d4ecf0ddc07

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_BlockSplit
import Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_KP_blockSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.KP
open Module
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.MainNotions.flipOneThree.Pf.KP
theorem _root_.solution : BlockSplit := by
  intro O _ _ _ J _ n z hz A h
  exact blockSplit n z hz A h
end Formalism.MainNotions.flipOneThree.Pf.KP

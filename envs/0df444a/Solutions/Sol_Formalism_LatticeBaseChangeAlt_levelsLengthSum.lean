-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.levelsLengthSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:58:48.478992+00:00
-- url     : https://prove2.me/submissions/2c405655-306f-47a5-b79f-8fe279497b46

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_LocalStepLevelsExt
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LengthResidueFieldBase
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LevelsChain
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LevelsLengthSum
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_filteredPoleLength


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LatticeBaseChangeAlt
open Module
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : LevelsLengthSum := by
  intro O' _ _ ι _ Rr A _ _ _ _ _ _ _ _ x mm n F r R h0 hn hmono hinj hlen hsum
  rw [Module.length_pi_of_fintype]
  refine Finset.sum_congr rfl fun z _ => ?_
  have h := filteredPoleLength O' (Rr z) (A z) (x z) (mm z) (n z) (F z) (r z) (h0 z) (hn z)
    (hmono z) (hinj z) (hlen z)
  rw [h, hsum z]
end Formalism.LatticeBaseChangeAlt

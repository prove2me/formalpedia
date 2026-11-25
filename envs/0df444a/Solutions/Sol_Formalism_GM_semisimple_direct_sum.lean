-- Prove2me | solution 1 for Formalism.GM.semisimple_direct_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:05:14.959101+00:00
-- url     : https://prove2.me/submissions/6711234e-140d-4c12-a763-2151f4cb22bb

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_Formalism_GM_M_ss_direct
import Theorems.Thm_Formalism_GM_M_ss_sat

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
theorem _root_.solution : Formalism.GM.M.SSDirect := by
  intro p _ N r _ D _ _
  exact ⟨Formalism.GM.M.ss_direct D, fun x hx hi => Formalism.GM.M.ss_sat D x hx hi⟩
end Formalism.GM

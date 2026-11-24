-- Prove2me | solution 1 for Formalism.GM.mahler_disc_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:26.993196+00:00
-- url     : https://prove2.me/submissions/7a65939f-d9da-41a2-aeee-84916ca1cb4e

import Definitions.Def_Formalism_MahlerMeasure_StatementB
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_Mahler
import Theorems.Thm_Formalism_GM_bB_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Polynomial
namespace Formalism.GM
theorem _root_.solution : MahlerDisc := by
  intro p k i t₀ hp hi n
  haveI : Fact p.Prime := ⟨hp⟩
  exact bB_mem p k i hi t₀ n
end Formalism.GM

-- Prove2me | solution 1 for Formalism.GM.TM.letters_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:16.499322+00:00
-- url     : https://prove2.me/submissions/2bd5d10a-e9df-4175-b372-bc02eef46dee

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {N : ℕ}
namespace Formalism.GM.TM
theorem _root_.solution {K : ℕ} {L1 L2 : Letters K} (hv : L1.vec = L2.vec) (hd : L1.deg = L2.deg) : L1 = L2 := by
  cases L1; cases L2; simp_all
end Formalism.GM.TM

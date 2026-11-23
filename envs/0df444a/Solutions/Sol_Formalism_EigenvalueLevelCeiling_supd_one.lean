-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.supd_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:41.7335+00:00
-- url     : https://prove2.me/submissions/6f58810b-97be-470f-8473-c68eae8531e6

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_Mirabolic
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_one_castSucc_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.EigenvalueLevelCeiling
variable {k : Type} [Field k] {n : ℕ}
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : supd (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = 0 := by
  simp [supd, one_castSucc_succ]
end Formalism.EigenvalueLevelCeiling

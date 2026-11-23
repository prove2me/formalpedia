-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.supd_pairU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:27.644778+00:00
-- url     : https://prove2.me/submissions/8ac830b3-e7b4-4030-abb1-28d88af7d2e1

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_Mirabolic
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_pairU_apply
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
theorem _root_.solution (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (t : k) :
    supd (pairU h s l t) = t * h s.castSucc l.castSucc := by
  simp [supd, pairU_apply, one_castSucc_succ, Fin.succ_inj]
end Formalism.EigenvalueLevelCeiling

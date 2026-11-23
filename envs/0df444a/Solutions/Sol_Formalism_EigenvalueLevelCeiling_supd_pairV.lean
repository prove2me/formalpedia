-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.supd_pairV
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:27.553557+00:00
-- url     : https://prove2.me/submissions/f35df5a3-b9a3-4381-86cc-569401e0494d

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_Mirabolic
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_pairV_apply
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
    supd (pairV h s l t) = t * h s.succ l.succ := by
  simp [supd, pairV_apply, one_castSucc_succ, Fin.castSucc_inj]
end Formalism.EigenvalueLevelCeiling

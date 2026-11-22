-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.pairV_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:12:31.923629+00:00
-- url     : https://prove2.me/submissions/75aef8bb-b0b9-481e-9883-ce9eed1e0e8a

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_Mirabolic

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
theorem _root_.solution (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (t : k) (a b) :
    pairV h s l t a b = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b +
      t * ((if a = l.castSucc then 1 else 0) * h s.succ b) := by
  simp [pairV, Matrix.vecMulVec_apply, Pi.single_apply]
end Formalism.EigenvalueLevelCeiling

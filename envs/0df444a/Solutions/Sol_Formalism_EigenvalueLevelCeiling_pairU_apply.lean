-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.pairU_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:27:00.693765+00:00
-- url     : https://prove2.me/submissions/a521bdcd-3bf9-4ccf-ba0f-6a92f3e06fc0

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
    pairU h s l t a b = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b +
      t * (h a l.castSucc * if b = s.succ then 1 else 0) := by
  simp [pairU, Matrix.vecMulVec_apply, Pi.single_apply]
end Formalism.EigenvalueLevelCeiling

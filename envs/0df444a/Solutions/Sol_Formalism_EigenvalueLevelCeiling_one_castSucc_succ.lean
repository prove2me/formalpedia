-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.one_castSucc_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:12:28.725272+00:00
-- url     : https://prove2.me/submissions/4a9064e8-11af-4544-9d92-850e2f9b1710

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
theorem _root_.solution (a : Fin n) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a.castSucc a.succ = 0 :=
  Matrix.one_apply_ne ((Fin.castSucc_lt_succ : a.castSucc < a.succ)).ne
end Formalism.EigenvalueLevelCeiling

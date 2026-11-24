-- Prove2me | solution 1 for Formalism.G0.TailSumsP.cnt_succ_some
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:12.378805+00:00
-- url     : https://prove2.me/submissions/3f2a56b2-d15f-4e39-8342-dc2022b7b618

import Definitions.Def_Formalism_SubspaceCounting_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TailSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
open Formalism.G0.TailSumsP
namespace Formalism.G0.TailSumsP
theorem _root_.solution (steps : List (Option ℕ)) (i j : ℕ) (hij : i ≤ j) (hj : j < steps.length)
    {B : ℕ} (h : steps[j] = some B) : cnt steps i (j + 1) = cnt steps i j + 1 := by
  unfold cnt
  rw [show j + 1 - i = (j - i) + 1 by omega, List.take_add_one, List.getElem?_drop,
    show i + (j - i) = j by omega, List.getElem?_eq_getElem hj, h]
  simp
end Formalism.G0.TailSumsP

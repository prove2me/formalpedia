-- Prove2me | solution 1 for FirstPassageLinearTransport.wordIncrementSum_rev
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:30.020859+00:00
-- url     : https://prove2.me/submissions/c00e2745-7e11-401c-be65-291d2325cc72

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_listIncrementSum_reverse
import Theorems.Thm_FirstPassageLinearTransport_ofFn_rev
import Theorems.Thm_FirstPassageLinearTransport_wordIncrementSum_eq_list

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r : ℕ} (x : Bool → ℝ) (v : Fin r → Bool) :
    wordIncrementSum x (fun i => v (Fin.rev i)) =
      wordIncrementSum x v := by
  rw [wordIncrementSum_eq_list, ofFn_rev, listIncrementSum_reverse,
    ← wordIncrementSum_eq_list]
end FirstPassageLinearTransport

-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.two_numDerangements_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:52:01.127153+00:00
-- url     : https://prove2.me/submissions/7267f94e-922c-4e0e-9483-c4b749ceaa06

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) : 2 * numDerangements n ≤ n.factorial := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, hn with
    | 1, _ => simp [numDerangements_one]
    | 2, _ => simp [numDerangements_add_two, numDerangements_zero, numDerangements_one, Nat.factorial]
    | k + 3, _ =>
      have h1 := ih (k + 1) (by omega) (by omega)
      have h2 := ih (k + 2) (by omega) (by omega)
      show 2 * numDerangements (k + 1 + 2) ≤ (k + 1 + 2).factorial
      rw [numDerangements_add_two, Nat.factorial_succ (k + 1 + 1)]
      rw [show k + 1 + 1 = k + 2 from rfl, Nat.factorial_succ (k + 1)] at *
      nlinarith [h1, h2]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

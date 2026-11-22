-- Prove2me | solution 1 for Formalism.G0.QVandermondeP.gb_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:27:19.336355+00:00
-- url     : https://prove2.me/submissions/9fc6339f-c675-4926-902b-569a58312bf0

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Theorems.Thm_Formalism_G0_QVandermondeP_gb_succ_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
open Formalism.G0.QVandermondeP
namespace Formalism.G0.QVandermondeP
theorem _root_.solution (q : ℕ) : ∀ n k : ℕ, n < k → gaussBinom q n k = 0
  | 0, 0, h => absurd h (lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k + 1, h => by
    rw [gb_succ_succ, solution q n k (by omega), solution q n (k + 1) (by omega)]
    simp
end Formalism.G0.QVandermondeP

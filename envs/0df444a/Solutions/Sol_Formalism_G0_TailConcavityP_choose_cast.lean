-- Prove2me | solution 1 for Formalism.G0.TailConcavityP.choose_cast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:11.182962+00:00
-- url     : https://prove2.me/submissions/7a9ad1bb-4307-4ca7-a5e9-0e9c00e4ef7f

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TailConcavity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.G0
open Formalism.G0.TailConcavityP
namespace Formalism.G0.TailConcavityP
theorem _root_.solution (y k : ℕ) :
    ((y + k).choose k : ℝ) = ∏ i ∈ range k, (((y : ℝ) + i + 1) / (i + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, ← ih]
    have h := Nat.add_one_mul_choose_eq (y + k) k
    have h2 : y + (k + 1) = y + k + 1 := by omega
    rw [h2]
    have h3 : (((y + k + 1).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) =
        ((y : ℝ) + k + 1) * (((y + k).choose k : ℕ) : ℝ) := by
      have := congrArg (fun n : ℕ => (n : ℝ)) h.symm
      push_cast at this
      linarith
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    rw [mul_div_assoc', eq_div_iff hk]
    linarith
end Formalism.G0.TailConcavityP

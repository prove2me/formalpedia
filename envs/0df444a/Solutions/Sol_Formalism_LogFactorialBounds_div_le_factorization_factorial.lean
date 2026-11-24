-- Prove2me | solution 1 for Formalism.LogFactorialBounds.div_le_factorization_factorial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:36:44.969988+00:00
-- url     : https://prove2.me/submissions/5aaf0122-8001-4d06-92af-b36f64d0b784

import Definitions.Def_Formalism_LogFactorialBounds_LocalFactorSplitDv
import Mathlib
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LogFactorialBounds
open Finset Real
namespace Formalism.LogFactorialBounds
theorem _root_.solution {p : ℕ} (hp : p.Prime) (n : ℕ) :
    n / p ≤ (n.factorial).factorization p := by
  rcases Nat.lt_or_ge n p with h | h
  · rw [Nat.div_eq_of_lt h]
    exact Nat.zero_le _
  · rw [Nat.factorization_factorial hp (Nat.lt_succ_self (Nat.log p n))]
    have hpos : 0 < Nat.log p n := Nat.log_pos hp.one_lt h
    have h1 : 1 ∈ Finset.Ico 1 (Nat.succ (Nat.log p n)) :=
      Finset.mem_Ico.2 ⟨le_rfl, by omega⟩
    have := Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) h1
    simpa using this
end Formalism.LogFactorialBounds

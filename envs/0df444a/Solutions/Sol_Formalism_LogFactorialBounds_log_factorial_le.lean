-- Prove2me | solution 1 for Formalism.LogFactorialBounds.log_factorial_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:36:45.776258+00:00
-- url     : https://prove2.me/submissions/cf9116e6-8c06-40b5-83d1-7719f172fdfb

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
theorem _root_.solution (n : ℕ) : Real.log (n.factorial : ℕ) ≤ n * Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : (0 : ℝ) < (n.factorial : ℕ) := by exact_mod_cast Nat.factorial_pos n
    have h2 : ((n.factorial : ℕ) : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    calc Real.log (n.factorial : ℕ) ≤ Real.log ((n : ℝ) ^ n) := Real.log_le_log h1 h2
      _ = n * Real.log n := by rw [Real.log_pow]
end Formalism.LogFactorialBounds

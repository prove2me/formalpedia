-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.weyl_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:16:49.306583+00:00
-- url     : https://prove2.me/submissions/d0b6fe72-7d6d-4e36-9f77-cfc255b3f66d

import Definitions.Def_Formalism_BranchSandwichDivisors_NormLog
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Interlace
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Numeric
import Theorems.Thm_Formalism_BranchingDeterminantCap_weyl_dimension_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution : WeylLog := by
  unfold WeylLog
  intro n nu a h ha
  obtain ⟨h1, h2⟩ := weyl_dimension_bound n nu h
  have hM : (0:ℝ) ≤ ((nu 0 - nu (Fin.last n) : ℤ) : ℝ) := by
    have := h (Fin.zero_le (Fin.last n))
    exact_mod_cast (by omega : (0:ℤ) ≤ nu 0 - nu (Fin.last n))
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hK : (((n + 1) * n / 2 : ℕ) : ℝ) = ((n:ℝ) + 1) * ((n:ℝ) + 1 - 1) / 2 := by
    have hdvd : 2 ∣ (n + 1) * n := by
      rw [mul_comm]; exact even_iff_two_dvd.mp (Nat.even_mul_succ_self n)
    rw [Nat.cast_div hdvd (by norm_num)]; push_cast; ring
  calc Real.log _ ≤ Real.log ((2 * a) ^ ((n + 1) * n / 2)) := by
        apply Real.log_le_log (by linarith)
        calc _ ≤ _ := h2
          _ ≤ (2 * a) ^ ((n + 1) * n / 2) := by gcongr <;> linarith
    _ = _ := by rw [Real.log_pow, hK]
end Formalism.BranchingDeterminantCap

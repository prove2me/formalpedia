-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.sum_log_div_le_log_add_log_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:39:07.055806+00:00
-- url     : https://prove2.me/submissions/c27bbe48-a1ca-4d31-8a4e-e8ad64e379e2

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_log_prime_nonneg
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_sum_div_mul_log_le_log_factorial__bf9748ec8161
import Theorems.Thm_Formalism_RankGapBounds_ChebyshevFactorialBounds_chebyshevThetaLe_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo n, Real.log (p : ℝ) / (p : ℝ) ≤
      Real.log (n : ℝ) + Real.log 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac : Real.log ((n.factorial : ℕ) : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
    have h1 : ((n.factorial : ℕ) : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    have h2 : (0 : ℝ) < ((n.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos n
    calc Real.log ((n.factorial : ℕ) : ℝ) ≤ Real.log ((n : ℝ) ^ n) := Real.log_le_log h2 h1
      _ = (n : ℝ) * Real.log (n : ℝ) := Real.log_pow _ _
  have key : (n : ℝ) * ∑ p ∈ Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo n, Real.log (p : ℝ) / (p : ℝ) ≤
      (n : ℝ) * (Real.log (n : ℝ) + Real.log 4) := by
    calc (n : ℝ) * ∑ p ∈ Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo n, Real.log (p : ℝ) / (p : ℝ)
        = ∑ p ∈ Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo n, (n : ℝ) / (p : ℝ) * Real.log (p : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _
          ring
      _ ≤ ∑ p ∈ Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo n, (((n / p : ℕ) : ℝ) + 1) * Real.log (p : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          have hp' : p.Prime := (Finset.mem_filter.1 hp).2
          have h1 := Nat.lt_floor_add_one ((n : ℝ) / (p : ℝ))
          rw [Nat.floor_div_eq_div] at h1
          exact mul_le_mul_of_nonneg_right h1.le (log_prime_nonneg hp')
      _ = ∑ p ∈ Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo n, ((n / p : ℕ) : ℝ) * Real.log (p : ℝ)
          + ∑ p ∈ Formalism.RankGapBounds.ChebyshevFactorialBounds.primesUpTo n, Real.log (p : ℝ) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro p _
          ring
      _ ≤ Real.log ((n.factorial : ℕ) : ℝ) + Real.log 4 * (n : ℝ) :=
          add_le_add (sum_div_mul_log_le_log_factorial' n) (Formalism.RankGapBounds.ChebyshevFactorialBounds.chebyshevThetaLe_holds n)
      _ ≤ (n : ℝ) * (Real.log (n : ℝ) + Real.log 4) := by linarith
  exact le_of_mul_le_mul_left key hn0
end Formalism.CohomologicalDescent.LogSmallConstantBounds

-- Prove2me | solution 1 for Formalism.LogFactorialBounds.sum_div_mul_log_le_log_factorial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:51:19.477804+00:00
-- url     : https://prove2.me/submissions/4aeb3b33-b69a-4867-8869-a83baf2396af

import Definitions.Def_Formalism_LogFactorialBounds_LocalFactorSplitDv
import Mathlib
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Theorems.Thm_Formalism_LogFactorialBounds_div_le_factorization_factorial

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
theorem _root_.solution (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p ≤ Real.log (n.factorial : ℕ) := by
  have key : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) →
      ∏ p ∈ s, p ^ (n / p) ∣ n.factorial := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _
      simp
    · intro a s ha ih h
      rw [Finset.prod_insert ha]
      have hs := ih (fun p hp => h p (Finset.mem_insert_of_mem hp))
      have haP := h a (Finset.mem_insert_self a s)
      have hcop : Nat.Coprime (a ^ (n / a)) (∏ p ∈ s, p ^ (n / p)) := by
        apply Nat.Coprime.pow_left
        apply Nat.Coprime.prod_right
        intro p hp
        apply Nat.Coprime.pow_right
        exact (Nat.coprime_primes haP (h p (Finset.mem_insert_of_mem hp))).2
          (fun e => ha (by rw [e]; exact hp))
      exact hcop.mul_dvd_of_dvd_of_dvd
        ((haP.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero n)).2
          (div_le_factorization_factorial haP n)) hs
  have hd : ∏ p ∈ Nat.primesLE n, p ^ (n / p) ∣ n.factorial :=
    key _ (fun p hp => (Nat.mem_primesLE.1 hp).2)
  have hle : ((∏ p ∈ Nat.primesLE n, p ^ (n / p) : ℕ) : ℝ) ≤ (n.factorial : ℕ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos n) hd
  have hpos : (0 : ℝ) < ((∏ p ∈ Nat.primesLE n, p ^ (n / p) : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun p hp => pow_pos (Nat.mem_primesLE.1 hp).2.pos _)
  have hlog : Real.log ((∏ p ∈ Nat.primesLE n, p ^ (n / p) : ℕ) : ℝ)
      = ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p := by
    rw [Nat.cast_prod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro p _
      rw [Nat.cast_pow, Real.log_pow]
    · intro p hp
      have : (0 : ℝ) < p := by exact_mod_cast (Nat.mem_primesLE.1 hp).2.pos
      rw [Nat.cast_pow]
      exact pow_ne_zero _ this.ne'
  rw [← hlog]
  exact Real.log_le_log hpos hle
end Formalism.LogFactorialBounds

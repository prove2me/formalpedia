-- Prove2me | solution 1 for Formalism.RankGapBounds.ChebyshevFactorialBounds.sumLogDivPredLe_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:21:51.255435+00:00
-- url     : https://prove2.me/submissions/675f90a7-93d0-42f5-aa26-d75932574436

import Definitions.Def_Formalism_RankGapBounds_LargePrimeFactor
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Theorems.Thm_Formalism_RankGapBounds_ChebyshevFactorialBounds_chebyshevThetaLe_holds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Real Finset
namespace Formalism.RankGapBounds.ChebyshevFactorialBounds
private theorem prod_primes_pow_div_dvd_factorial (n : ℕ) : ∏ p ∈ primesUpTo n, p ^ (n / p) ∣ n.factorial := by
  have key : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → ∏ p ∈ s, p ^ (n / p) ∣ n.factorial := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | @insert a s ha ih =>
      intro hs
      rw [Finset.prod_insert ha]
      have hpa : a.Prime := hs a (Finset.mem_insert_self a s)
      have hs' : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
      refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ ?_ (ih hs')
      · exact Nat.Coprime.prod_right fun p hp =>
          Nat.Coprime.pow _ _ ((Nat.coprime_primes hpa (hs' p hp)).mpr fun h => ha (h ▸ hp))
      · rw [hpa.pow_dvd_factorial_iff (show Nat.log a n < Nat.log a n + 2 by omega)]
        calc n / a = n / a ^ 1 := by rw [pow_one]
          _ ≤ ∑ i ∈ Finset.Ico 1 (Nat.log a n + 2), n / a ^ i :=
            Finset.single_le_sum (f := fun i => n / a ^ i) (fun _ _ => Nat.zero_le _)
              (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
  exact key _ fun p hp => (Finset.mem_filter.mp hp).2
private theorem sum_primes_log_div_le_log_add_log_four (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ primesUpTo n, Real.log p / p ≤ Real.log n + Real.log 4 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : ∀ p ∈ primesUpTo n, (0 : ℝ) < p := fun p hp => by
    exact_mod_cast (Finset.mem_filter.mp hp).2.pos
  have h1 : ∑ p ∈ primesUpTo n, ((n / p : ℕ) : ℝ) * Real.log p ≤ (n : ℝ) * Real.log n := by
    have hd := Nat.le_of_dvd (Nat.factorial_pos n) (prod_primes_pow_div_dvd_factorial n)
    have hprod : (0 : ℝ) < ∏ p ∈ primesUpTo n, (p : ℝ) ^ (n / p) :=
      Finset.prod_pos fun p hp => pow_pos (hpos p hp) _
    calc ∑ p ∈ primesUpTo n, ((n / p : ℕ) : ℝ) * Real.log p
        = Real.log (∏ p ∈ primesUpTo n, (p : ℝ) ^ (n / p)) := by
          rw [Real.log_prod fun p hp => (pow_pos (hpos p hp) _).ne']
          simp only [Real.log_pow]
      _ ≤ Real.log (n.factorial : ℝ) := Real.log_le_log hprod (by exact_mod_cast hd)
      _ ≤ Real.log ((n : ℝ) ^ n) :=
          Real.log_le_log (by exact_mod_cast Nat.factorial_pos n) (by exact_mod_cast Nat.factorial_le_pow n)
      _ = n * Real.log n := Real.log_pow _ _
  have h2 : ∑ p ∈ primesUpTo n, Real.log p ≤ Real.log 4 * n := chebyshevThetaLe_holds n
  have h3 : ∀ p ∈ primesUpTo n,
      (n : ℝ) * (Real.log p / p) ≤ ((n / p : ℕ) : ℝ) * Real.log p + Real.log p := by
    intro p hp
    have hlog : 0 ≤ Real.log p :=
      Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
    have hfl : (n : ℝ) / p ≤ ((n / p : ℕ) : ℝ) + 1 := by
      rw [← Nat.floor_div_eq_div (K := ℝ)]
      exact (Nat.lt_floor_add_one _).le
    calc (n : ℝ) * (Real.log p / p) = (n : ℝ) / p * Real.log p := by ring
      _ ≤ (((n / p : ℕ) : ℝ) + 1) * Real.log p := mul_le_mul_of_nonneg_right hfl hlog
      _ = ((n / p : ℕ) : ℝ) * Real.log p + Real.log p := by ring
  have hsum : (n : ℝ) * ∑ p ∈ primesUpTo n, Real.log p / p ≤ n * (Real.log n + Real.log 4) := by
    rw [Finset.mul_sum]
    calc ∑ p ∈ primesUpTo n, (n : ℝ) * (Real.log p / p)
        ≤ ∑ p ∈ primesUpTo n, (((n / p : ℕ) : ℝ) * Real.log p + Real.log p) := Finset.sum_le_sum h3
      _ = ∑ p ∈ primesUpTo n, ((n / p : ℕ) : ℝ) * Real.log p + ∑ p ∈ primesUpTo n, Real.log p :=
          Finset.sum_add_distrib
      _ ≤ n * Real.log n + Real.log 4 * n := add_le_add h1 h2
      _ = n * (Real.log n + Real.log 4) := by ring
  exact le_of_mul_le_mul_left hsum hn'
end Formalism.RankGapBounds.ChebyshevFactorialBounds
end

set_option autoImplicit false
open Real Finset
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.ChebyshevFactorialBounds
namespace Formalism.RankGapBounds.ChebyshevFactorialBounds
theorem _root_.solution : MertensType := by
  refine ⟨6, fun n hn => ?_⟩
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (by exact_mod_cast hn)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hS := sum_primes_log_div_le_log_add_log_four n (by omega)
  have hterm : ∀ p ∈ primesUpTo n, Real.log p / ((p : ℝ) - 1) ≤ 2 * (Real.log p / p) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < p - 1)]
    have hd : 2 * (Real.log p / p) * (p - 1) - Real.log p = Real.log p * (p - 2) / p := by
      field_simp
      ring
    have : 0 ≤ Real.log p * (p - 2) / p := div_nonneg (mul_nonneg hlog (by linarith)) (by linarith)
    linarith
  calc ∑ p ∈ primesUpTo n, Real.log p / ((p : ℝ) - 1)
      ≤ ∑ p ∈ primesUpTo n, 2 * (Real.log p / p) := Finset.sum_le_sum hterm
    _ = 2 * ∑ p ∈ primesUpTo n, Real.log p / p := by rw [Finset.mul_sum]
    _ ≤ 2 * (Real.log n + Real.log 4) := by linarith
    _ ≤ 6 * Real.log n := by rw [h4]; linarith
end Formalism.RankGapBounds.ChebyshevFactorialBounds

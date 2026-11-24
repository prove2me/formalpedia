-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.minkowski_number_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:41.354811+00:00
-- url     : https://prove2.me/submissions/484f95cb-1010-41dd-9d29-ad50fd782f82

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IdealsOfNormEqIndexSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
private theorem prod_pow_dvd_lemma (S : Finset ℕ) (e : ℕ → ℕ) (n : ℕ) :
    (∀ p ∈ S, p.Prime) → (∀ p ∈ S, p ^ e p ∣ n) → ∏ p ∈ S, p ^ e p ∣ n := by
  refine Finset.induction_on S (by simp) ?_
  intro a S ha ih hS h
  rw [Finset.prod_insert ha]
  apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
  · apply Nat.Coprime.prod_right
    intro q hq
    apply Nat.Coprime.pow
    exact (Nat.coprime_primes (hS a (by simp)) (hS q (by simp [hq]))).2
      (by rintro rfl; exact ha hq)
  · exact h a (by simp)
  · exact ih (fun p hp => hS p (by simp [hp])) (fun p hp => h p (by simp [hp]))
open Formalism.SLP.P.CountO NumberField
open scoped nonZeroDivisors
open NumberField Formalism.SLP.P.CountO
end Formalism.HermitianLatticeCounting.P
end

set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : MinkowskiNumberDvd := by
  intro N
  unfold minkowskiNumber
  apply prod_pow_dvd_lemma
  · intro p hp; exact (Finset.mem_filter.1 hp).2
  intro p hpS
  have hp : p.Prime := (Finset.mem_filter.1 hpS).2
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h2 : N < 2 ^ N := by
    clear hpS hp hN
    induction N with
    | zero => simp
    | succ k ih => rw [pow_succ]; omega
  have hlt : 2 * N < p ^ (N + 2) := by
    calc 2 * N < 2 ^ (N + 2) := by rw [pow_add]; omega
      _ ≤ p ^ (N + 2) := Nat.pow_le_pow_left hp.two_le _
  have hlog : Nat.log p (2 * N) < N + 2 := Nat.log_lt_of_lt_pow (by omega) hlt
  rw [hp.pow_dvd_factorial_iff hlog, Finset.sum_Ico_eq_sum_range]
  have e : N + 2 - 1 = N + 1 := by omega
  rw [e]
  apply Finset.sum_le_sum
  intro k _
  have hp2 := hp.two_le
  have hpk : 0 < p ^ k := pow_pos hp.pos k
  rw [Nat.le_div_iff_mul_le (pow_pos hp.pos _)]
  have h1 := Nat.div_mul_le_self N (p ^ k * (p - 1))
  have h3 : p ^ (1 + k) ≤ 2 * (p ^ k * (p - 1)) := by
    rw [pow_add, pow_one]
    have : p ≤ 2 * (p - 1) := by omega
    calc p * p ^ k ≤ 2 * (p - 1) * p ^ k := Nat.mul_le_mul_right _ this
      _ = 2 * (p ^ k * (p - 1)) := by ring
  calc N / (p ^ k * (p - 1)) * p ^ (1 + k)
      ≤ N / (p ^ k * (p - 1)) * (2 * (p ^ k * (p - 1))) := Nat.mul_le_mul_left _ h3
    _ = 2 * (N / (p ^ k * (p - 1)) * (p ^ k * (p - 1))) := by ring
    _ ≤ 2 * N := Nat.mul_le_mul_left _ h1
end Formalism.HermitianLatticeCounting.P

-- Prove2me | solution 1 for FrontierMathLean.dimitrovConjecture3_real_eq_iff_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:59:11.947251+00:00
-- url     : https://prove2.me/submissions/b6b08e1e-347b-49d1-9679-59374708102f

import Definitions.Def_FrontierMathLean_DimitrovConjecture3
import Definitions.Def_FrontierMathLean_DimitrovConjecture3Equality
import Theorems.Thm_FrontierMathLean_dedekindPsi_one
import Theorems.Thm_FrontierMathLean_dedekindPsi_prime
import Theorems.Thm_FrontierMathLean_dedekindPsi_zero
import Theorems.Thm_FrontierMathLean_nesbitt_paper_bound_eq_normalized
import Theorems.Thm_FrontierMathLean_normalized_nesbitt_ratio_eq_iff
import Theorems.Thm_FrontierMathLean_one_add_le_dedekindPsi
import Theorems.Thm_FrontierMathLean_one_add_le_sigmaOne
import Theorems.Thm_FrontierMathLean_totient_le_sub_one
attribute [local simp] FrontierMathLean.dedekindPsi_one
attribute [local simp] FrontierMathLean.dedekindPsi_zero


section
open scoped ArithmeticFunction.sigma
namespace FrontierMathLean
private theorem sigma_one_prime_for_conjecture3 {p : ℕ} (hp : p.Prime) :
    ArithmeticFunction.sigma 1 p = p + 1 := by
  simpa [Nat.add_comm] using
    (ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) hp)
private theorem first_variable_eq_of_nesbitt_power_equality
    {a b c u v : ℝ} {k : ℕ}
    (hk : 1 ≤ k) (ha : 0 < a) (hu : 0 < u)
    (hau : a ≤ u) (huv : u < v) (hvb : v ≤ b) (hvc : v ≤ c)
    (hEq :
      a ^ k / (b ^ k + c ^ k) +
          b ^ k / (a ^ k + c ^ k) +
          c ^ k / (a ^ k + b ^ k) =
        (4 * ((v / u) ^ k) ^ 2 + (v / u) ^ k + 1) /
          (2 * (((v / u) ^ k) ^ 2 + (v / u) ^ k))) :
    a = u := by
  have hv : 0 < v := lt_trans hu huv
  have hb : 0 < b := lt_of_lt_of_le hv hvb
  have hc : 0 < c := lt_of_lt_of_le hv hvc
  have hA : 0 < a ^ k := pow_pos ha k
  have hB : 0 < b ^ k := pow_pos hb k
  have hC : 0 < c ^ k := pow_pos hc k
  have hratio_one : 1 < v / u := (one_lt_div hu).2 huv
  have hr : 1 < (v / u) ^ k := by
    simpa using pow_lt_pow_left₀ hratio_one (by positivity) (Nat.ne_of_gt hk)
  have hratio_base_B : v / u ≤ b / a := by
    apply (div_le_div_iff₀ hu ha).2
    calc
      v * a ≤ b * a := mul_le_mul_of_nonneg_right hvb ha.le
      _ ≤ b * u := mul_le_mul_of_nonneg_left hau hb.le
  have hratio_base_C : v / u ≤ c / a := by
    apply (div_le_div_iff₀ hu ha).2
    calc
      v * a ≤ c * a := mul_le_mul_of_nonneg_right hvc ha.le
      _ ≤ c * u := mul_le_mul_of_nonneg_left hau hc.le
  have hrB : (v / u) ^ k ≤ b ^ k / a ^ k := by
    rw [← div_pow]
    exact pow_le_pow_left₀ (div_pos hv hu).le hratio_base_B k
  have hrC : (v / u) ^ k ≤ c ^ k / a ^ k := by
    rw [← div_pow]
    exact pow_le_pow_left₀ (div_pos hv hu).le hratio_base_C k
  have hExpand :
      1 / (b ^ k / a ^ k + c ^ k / a ^ k) +
          (b ^ k / a ^ k) / (1 + c ^ k / a ^ k) +
          (c ^ k / a ^ k) / (1 + b ^ k / a ^ k) =
        a ^ k / (b ^ k + c ^ k) +
          b ^ k / (a ^ k + c ^ k) +
          c ^ k / (a ^ k + b ^ k) := by
    field_simp [hA.ne', hB.ne', hC.ne']
  have hNormalized :
      1 / (b ^ k / a ^ k + c ^ k / a ^ k) +
          (b ^ k / a ^ k) / (1 + c ^ k / a ^ k) +
          (c ^ k / a ^ k) / (1 + b ^ k / a ^ k) =
        (4 * ((v / u) ^ k) ^ 2 + (v / u) ^ k + 1) /
          (2 * (((v / u) ^ k) ^ 2 + (v / u) ^ k)) :=
    hExpand.trans hEq
  have hratio_eq : b ^ k / a ^ k = (v / u) ^ k :=
    (normalized_nesbitt_ratio_eq_iff hr hrB hrC).mp hNormalized |>.1
  apply le_antisymm hau
  by_contra hnot
  have hau_strict : a < u := lt_of_not_ge hnot
  have hratio_strict : v / u < b / a := by
    apply (div_lt_div_iff₀ hu ha).2
    calc
      v * a < v * u := mul_lt_mul_of_pos_left hau_strict hv
      _ ≤ b * u := mul_le_mul_of_nonneg_right hvb hu.le
  have hpow_strict : (v / u) ^ k < (b / a) ^ k :=
    pow_lt_pow_left₀ hratio_strict (div_pos hv hu).le (Nat.ne_of_gt hk)
  have hpow_strict' : (v / u) ^ k < b ^ k / a ^ k :=
    hpow_strict.trans_eq (div_pow b a k)
  rw [hratio_eq] at hpow_strict'
  exact (lt_irrefl _ hpow_strict')
end FrontierMathLean
end

set_option autoImplicit false
open scoped ArithmeticFunction.sigma
open FrontierMathLean
namespace FrontierMathLean
theorem _root_.solution
    (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    ((4 * ((n : ℝ) + 1) ^ (2 * k)
            + (((n : ℝ) ^ 2 - 1) ^ k)
            + ((n : ℝ) - 1) ^ (2 * k)) /
          (2 * (((n : ℝ) + 1) ^ (2 * k)
            + (((n : ℝ) ^ 2 - 1) ^ k))) =
        (n.totient : ℝ) ^ k /
            ((dedekindPsi n : ℝ) ^ k
              + (ArithmeticFunction.sigma 1 n : ℝ) ^ k) +
          (dedekindPsi n : ℝ) ^ k /
            ((n.totient : ℝ) ^ k
              + (ArithmeticFunction.sigma 1 n : ℝ) ^ k) +
          (ArithmeticFunction.sigma 1 n : ℝ) ^ k /
            ((n.totient : ℝ) ^ k + (dedekindPsi n : ℝ) ^ k)) ↔
      n.Prime := by
  have hnpos : 0 < n := by omega
  have hcast_sub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have htotient_pos_nat : 0 < n.totient := Nat.totient_pos.mpr hnpos
  have htotient_pos : (0 : ℝ) < n.totient := by
    exact_mod_cast htotient_pos_nat
  have htotient_le : (n.totient : ℝ) ≤ (n : ℝ) - 1 := by
    rw [← hcast_sub]
    exact_mod_cast totient_le_sub_one hn
  have hu : (0 : ℝ) < (n : ℝ) - 1 := by
    rw [← hcast_sub]
    exact_mod_cast (show 0 < n - 1 by omega)
  have hv : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have huv : (n : ℝ) - 1 < (n : ℝ) + 1 := by linarith
  have hpsi : (n : ℝ) + 1 ≤ dedekindPsi n := by
    exact_mod_cast one_add_le_dedekindPsi hn
  have hsigma : (n : ℝ) + 1 ≤ ArithmeticFunction.sigma 1 n := by
    exact_mod_cast one_add_le_sigmaOne hn
  have hfactor : (n : ℝ) ^ 2 - 1 = ((n : ℝ) - 1) * ((n : ℝ) + 1) := by
    ring
  constructor
  · intro hEq
    have hBound :
        (4 * ((n : ℝ) + 1) ^ (2 * k)
              + (((n : ℝ) ^ 2 - 1) ^ k)
              + ((n : ℝ) - 1) ^ (2 * k)) /
            (2 * (((n : ℝ) + 1) ^ (2 * k)
              + (((n : ℝ) ^ 2 - 1) ^ k))) =
          (4 * ((((n : ℝ) + 1) / ((n : ℝ) - 1)) ^ k) ^ 2
              + (((n : ℝ) + 1) / ((n : ℝ) - 1)) ^ k + 1) /
            (2 * (((((n : ℝ) + 1) / ((n : ℝ) - 1)) ^ k) ^ 2
              + (((n : ℝ) + 1) / ((n : ℝ) - 1)) ^ k)) := by
      rw [hfactor]
      exact nesbitt_paper_bound_eq_normalized hu hv k
    have hNesbitt :
        (n.totient : ℝ) ^ k /
              ((dedekindPsi n : ℝ) ^ k
                + (ArithmeticFunction.sigma 1 n : ℝ) ^ k) +
            (dedekindPsi n : ℝ) ^ k /
              ((n.totient : ℝ) ^ k
                + (ArithmeticFunction.sigma 1 n : ℝ) ^ k) +
            (ArithmeticFunction.sigma 1 n : ℝ) ^ k /
              ((n.totient : ℝ) ^ k + (dedekindPsi n : ℝ) ^ k) =
          (4 * ((((n : ℝ) + 1) / ((n : ℝ) - 1)) ^ k) ^ 2
              + (((n : ℝ) + 1) / ((n : ℝ) - 1)) ^ k + 1) /
            (2 * (((((n : ℝ) + 1) / ((n : ℝ) - 1)) ^ k) ^ 2
              + (((n : ℝ) + 1) / ((n : ℝ) - 1)) ^ k)) :=
      hEq.symm.trans hBound
    have hphi_real : (n.totient : ℝ) = (n : ℝ) - 1 :=
      first_variable_eq_of_nesbitt_power_equality hk htotient_pos hu htotient_le
        huv hpsi hsigma hNesbitt
    have hphi_nat : n.totient = n - 1 := by
      exact_mod_cast (hphi_real.trans hcast_sub.symm)
    exact (Nat.totient_eq_iff_prime hnpos).mp hphi_nat
  · intro hp
    have hphi_prime : (n.totient : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.totient_prime hp, Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    have hpsi_prime : (dedekindPsi n : ℝ) = (n : ℝ) + 1 := by
      exact_mod_cast dedekindPsi_prime hp
    have hsigma_prime : (ArithmeticFunction.sigma 1 n : ℝ) = (n : ℝ) + 1 := by
      exact_mod_cast sigma_one_prime_for_conjecture3 hp
    rw [hphi_prime, hpsi_prime, hsigma_prime, hfactor,
      nesbitt_paper_bound_eq_normalized hu hv k, div_pow]
    field_simp [hu.ne', hv.ne']
    ring
end FrontierMathLean

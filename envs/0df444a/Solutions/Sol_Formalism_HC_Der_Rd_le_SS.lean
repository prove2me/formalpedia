-- Prove2me | solution 1 for Formalism.HC.Der.Rd.le_SS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:19.473314+00:00
-- url     : https://prove2.me/submissions/83347d7d-afb5-4527-8f5e-cc2841314f8e

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdBound
import Theorems.Thm_Formalism_HC_Der_Rd_rho_two
import Theorems.Thm_Formalism_HC_Der_Rd_rho_nonneg
import Theorems.Thm_Formalism_HC_Der_Rd_sum_totient_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ArithmeticFunction Finset
noncomputable section
namespace Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ)
private theorem exists_two_pow_mul_odd_of_le_of_ne_zero (k : ℕ) :
    ∀ n : ℕ, n ≤ k → n ≠ 0 → ∃ v M : ℕ, ¬ 2 ∣ M ∧ n = 2 ^ v * M := by
  induction k with
  | zero => intro n h1 h2; exact absurd (Nat.le_zero.mp h1) h2
  | succ k ih =>
    intro n h1 h2
    by_cases h : 2 ∣ n
    · obtain ⟨j, rfl⟩ := h
      obtain ⟨v, M, hM, hj⟩ := ih j (by omega) (by omega)
      exact ⟨v + 1, M, hM, by rw [hj, pow_succ]; ring⟩
    · exact ⟨0, n, h, by simp⟩
private theorem sum_range_ite_lt_two_eq_two (e : ℕ) :
    ∑ i ∈ range (e + 2), (if i < 2 then (1 : ℝ) else 0) = 2 := by
  induction e with
  | zero =>
    show ∑ i ∈ range 2, (if i < 2 then (1 : ℝ) else 0) = 2
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  | succ k ih =>
    rw [show k + 1 + 2 = k + 2 + 1 from rfl, Finset.sum_range_succ, ih, if_neg (by omega), add_zero]
end Formalism.HC.Der.Rd
end
end

set_option autoImplicit false
open ArithmeticFunction Finset
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ)
namespace Formalism.HC.Der.Rd
theorem _root_.solution {e d : ℕ} (h2 : 2 ^ (e + 2) ∣ N) (hd : d.Prime) (hdN : d ∣ N) (hd2 : ¬ 2 ∣ d)
    (hU : ∀ u ∈ U, ZMod.unitsMap h2 u = 1 ∨ ZMod.unitsMap h2 u = -1) (rd : 1 / 2 ≤ rho U (N / d)) :
    ((e : ℝ) + 1 - 1 / 2 ^ e) * Real.log 2 + Real.log d / 2 ≤ SS U := by
  classical
  have hN0 : N ≠ 0 := NeZero.ne N
  obtain ⟨v, M, hModd, hNvM⟩ := exists_two_pow_mul_odd_of_le_of_ne_zero N N le_rfl hN0
  have hM : Nat.Coprime 2 M := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hModd
  have hv : e + 2 ≤ v := by
    have h1 : 2 ^ (e + 2) ∣ 2 ^ v * M := by rw [← hNvM]; exact h2
    have h3 : 2 ^ (e + 2) ∣ 2 ^ v := (Nat.Coprime.pow_left (e + 2) hM).dvd_of_dvd_mul_right h1
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h3
  have hN' : 2 ^ (e + 2) * M ∣ N := by
    rw [hNvM]; exact Nat.mul_dvd_mul_right (pow_dvd_pow 2 hv) M
  have hU' : ∀ u ∈ U, ZMod.unitsMap ((dvd_mul_right _ M).trans hN') u = 1 ∨
      ZMod.unitsMap ((dvd_mul_right _ M).trans hN') u = -1 := hU
  have hdiv : ∀ i ∈ range (e + 2), N / 2 ^ (v - i) = 2 ^ i * M := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : N = 2 ^ (v - i) * (2 ^ i * M) := by
      rw [hNvM, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega)]
    rw [h1, Nat.mul_div_cancel_left _ (by positivity)]
  have hΛ2 : ∀ i ∈ range (e + 2), vonMangoldt (2 ^ (v - i)) = Real.log 2 := by
    intro i hi
    rw [Finset.mem_range] at hi
    simp [vonMangoldt_apply_pow (show v - i ≠ 0 by omega), vonMangoldt_apply_prime Nat.prime_two]
  have hSsub : insert d ((range (e + 2)).image (fun i => 2 ^ (v - i))) ⊆ N.divisors := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_image] at hx
    rw [Nat.mem_divisors]
    refine ⟨?_, hN0⟩
    rcases hx with rfl | ⟨i, _, rfl⟩
    · exact hdN
    · rw [hNvM]; exact (pow_dvd_pow 2 (Nat.sub_le v i)).trans (dvd_mul_right _ M)
  have hdS : d ∉ (range (e + 2)).image (fun i => 2 ^ (v - i)) := by
    rw [Finset.mem_image]
    rintro ⟨i, hi, hid⟩
    rw [Finset.mem_range] at hi
    apply hd2
    rw [← hid]
    exact dvd_pow_self 2 (by omega)
  have hinj : ∀ x ∈ range (e + 2), ∀ y ∈ range (e + 2), 2 ^ (v - x) = 2 ^ (v - y) → x = y := by
    intro x hx y hy hxy
    rw [Finset.mem_range] at hx hy
    have := Nat.pow_right_injective (le_refl 2) hxy
    omega
  have h1 : ∑ i ∈ range (e + 2), Real.log 2 * (1 - (((2 ^ i).totient : ℝ) + if i < 2 then 1 else 0) / 2 ^ (e + 1))
      ≤ ∑ i ∈ range (e + 2), vonMangoldt (2 ^ (v - i)) * rho U (N / 2 ^ (v - i)) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [hΛ2 i hi, hdiv i hi]
    have hie : i ≤ e + 2 := by rw [Finset.mem_range] at hi; omega
    exact mul_le_mul_of_nonneg_left (rho_two U hM hN' hie hU')
      (Real.log_nonneg one_le_two)
  have h2' : ∑ i ∈ range (e + 2), vonMangoldt (2 ^ (v - i)) * rho U (N / 2 ^ (v - i))
      = ∑ m ∈ (range (e + 2)).image (fun i => 2 ^ (v - i)),
          vonMangoldt m * rho U (N / m) :=
    (Finset.sum_image (f := fun m => vonMangoldt m * rho U (N / m)) hinj).symm
  have h3 : ∑ m ∈ insert d ((range (e + 2)).image (fun i => 2 ^ (v - i))),
        vonMangoldt m * rho U (N / m)
      ≤ ∑ m ∈ N.divisors, vonMangoldt m * rho U (N / m) :=
    Finset.sum_le_sum_of_subset_of_nonneg hSsub
      (fun m _ _ => mul_nonneg vonMangoldt_nonneg (rho_nonneg U _))
  rw [Finset.sum_insert hdS, vonMangoldt_apply_prime hd] at h3
  have hφ : ∑ i ∈ range (e + 2), (((2 ^ i).totient : ℕ) : ℝ) = 2 ^ (e + 1) := by
    have h := sum_totient_pow Nat.prime_two (e + 1)
    rw [show e + 1 + 1 = e + 2 from rfl] at h
    exact_mod_cast h
  have hsum : ∑ i ∈ range (e + 2), Real.log 2 * (1 - (((2 ^ i).totient : ℝ) + if i < 2 then 1 else 0) / 2 ^ (e + 1))
      = ((e : ℝ) + 1 - 1 / 2 ^ e) * Real.log 2 := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib,
      sum_range_ite_lt_two_eq_two e, hφ]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    field_simp
    ring
  have hd' : Real.log d / 2 ≤ Real.log d * rho U (N / d) := by
    have := mul_le_mul_of_nonneg_left rd (Real.log_nonneg (show (1 : ℝ) ≤ d by exact_mod_cast hd.one_lt.le))
    linarith
  unfold SS
  linarith [h1, h2', h3, hsum, hd']
end Formalism.HC.Der.Rd

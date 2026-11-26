-- Prove2me | solution 1 for GRH.initial_gap_test_misses_large_primes_and_height_three
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T16:16:43.478487+00:00
-- url     : https://prove2.me/submissions/25073f9e-88c0-41d1-b35d-0f8b9b408fc9

import Definitions.Def_GRH_DirichletPeriod
import Theorems.Thm_GRH_initial_gap_period_witness_limits
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open GRH.DirichletPeriod

private lemma no_cover (d : ℕ) (a H : ℝ) (h0 : 0<a) (ha : a ≤ 1)
    (reason : (∃ p : ℕ, p.Prime ∧ 7 ≤ p ∧ p ∣ d) ∨ (a ≤ 5/8 ∧ 3 ≤ H)) :
    ¬ Covers d a H := by
  rintro ⟨Q,M,hQ,hd,_,gap,test⟩
  obtain ⟨small,_,primes⟩ := GRH.initial_gap_period_witness_limits Q M a H hQ ha gap test
  rcases reason with ⟨p,prime,hp,hdp⟩ | ⟨edge,height⟩
  · have e := primes p prime (hdp.trans hd)
    omega
  · have ratio : 24/5 ≤ H/a := (le_div_iff₀ h0).2 (by linarith)
    have root : 24/5 ≤ Real.sqrt (1+(H/a)^2) := by
      have e := Real.sq_sqrt (show 0 ≤ 1+(H/a)^2 by positivity)
      nlinarith [Real.sqrt_nonneg (1+(H/a)^2),mul_self_le_mul_self (by norm_num : 0 ≤ (24/5:ℝ)) ratio]
    have lower := mul_le_mul_of_nonneg_left (add_le_add_left root 1)
      (show (0:ℝ) ≤ (Q.totient:ℝ)/4 by positivity)
    by_cases hm : M ≤ 4
    · obtain ⟨b,hb⟩ := Nat.totient_even hQ
      have pos := Nat.totient_pos.mpr (show 0<Q by omega)
      have ph : (2:ℝ) ≤ Q.totient := by exact_mod_cast (show 2 ≤ Q.totient by omega)
      have cap : (5:ℝ)^((5/8):ℝ) ≤ 14/5 := by
        apply le_of_pow_le_pow_left₀ (n:=8) (by decide) (by norm_num)
        rw [← Real.rpow_mul_natCast (by norm_num)]
        norm_num
      have m : (M:ℝ)+1 ≤ 5 := by exact_mod_cast (show M+1 ≤ 5 by omega)
      have up := (Real.rpow_le_rpow (show (0:ℝ) ≤ (M:ℝ)+1 by positivity) m h0.le).trans
        ((Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 5) edge).trans cap)
      linarith
    · have three : 3 ∣ Q := (by decide : Nat.Prime 3).dvd_iff_not_coprime.mpr (gap 3 (by decide) (by omega))
      have five : 5 ∣ Q := (by decide : Nat.Prime 5).dvd_iff_not_coprime.mpr (gap 5 (by decide) (by omega))
      have e : 15 ∣ Q := (by decide : Nat.Coprime 3 5).mul_dvd_of_dvd_of_dvd three five
      have hp := Nat.le_of_dvd (Nat.totient_pos.mpr (show 0<Q by omega)) (Nat.totient_dvd_of_dvd e)
      rw [show (15:ℕ).totient=8 by decide] at hp
      have ph : (8:ℝ) ≤ Q.totient := by exact_mod_cast hp
      have up := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ (M:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) M]) ha
      rw [Real.rpow_one] at up
      have m : (M:ℝ) ≤ 6 := by exact_mod_cast small
      linarith

/-- The initial-gap arithmetic test cannot reach any target grid of
height three or greater, or any level divisible by a prime at least seven. -/
theorem solution (d h : ℕ) (hc : (∃ p : ℕ, p.Prime ∧ 7 ≤ p ∧ p ∣ d) ∨ 2 ≤ h) :
    ¬ Covers d (1/2+((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) ((h:ℝ)+1) := by
  have hp : (0:ℝ) ≤ (0.8749570698:ℝ)-1/2 := by norm_num
  have hh : (1:ℝ) ≤ (h:ℝ)+1 := by linarith [Nat.cast_nonneg (α:=ℝ) h]
  have pos := div_nonneg hp (by positivity : 0 ≤ (h:ℝ)+1)
  have le := div_le_self hp hh
  apply no_cover d _ _ (by linarith) (by linarith)
  rcases hc with prime|high
  · exact Or.inl prime
  · have height : (3:ℝ) ≤ (h:ℝ)+1 := by exact_mod_cast (show 3 ≤ h+1 by omega)
    have small : ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1) ≤ 1/8 :=
      (div_le_iff₀ (by positivity)).2 (by linarith)
    exact Or.inr ⟨by linarith,height⟩

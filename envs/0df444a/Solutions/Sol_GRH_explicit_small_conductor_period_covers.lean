-- Prove2me | solution 1 for GRH.explicit_small_conductor_period_covers
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T15:34:44.645338+00:00
-- url     : https://prove2.me/submissions/28a194c0-eb09-41a3-997f-c3a3dccaa2e6

import Definitions.Def_GRH_DirichletPeriod
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open GRH.DirichletPeriod

private lemma fractional_power {x y : ℝ} (hy : 0 ≤ y) {p n : ℕ}
    (hn : 0 < n) (h : x^n < y^p) : x < y^((p:ℝ)/n) := by
  by_contra! bad
  have v := pow_le_pow_left₀ (Real.rpow_nonneg hy _) bad n
  rw [← Real.rpow_mul_natCast hy,div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hn.ne'),Real.rpow_natCast] at v
  linarith

private lemma witness {d Q M p n : ℕ} {a H B : ℝ} (hQ : 2 < Q) (hd : d ∣ Q) (hM : 0 < M)
    (hgap : ∀ k : ℕ, 2 ≤ k → k ≤ M → ¬ k.Coprime Q)
    (hn : 0 < n) (hexp : (p:ℝ)/n ≤ a)
    (hroot : Real.sqrt (1+(H/a)^2) ≤ B)
    (hpow : (((Q.totient:ℝ)/4)*(1+B))^n < ((M:ℝ)+1)^p) : Covers d a H := by
  refine ⟨Q,M,hQ,hd,hM,hgap,?_⟩
  have e := fractional_power (show 0 ≤ (M:ℝ)+1 by positivity) hn hpow
  exact ((mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hroot)
    (show 0 ≤ (Q.totient:ℝ)/4 by positivity)).trans_lt e).trans_le
    (Real.rpow_le_rpow_of_exponent_le (show 1 ≤ (M:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) M]) hexp)

private lemma root_bound {a H a0 H0 B : ℝ} (h0 : 0 < a0) (ha : a0 ≤ a)
    (hH : 0 ≤ H) (hH' : H ≤ H0) (hB : 0 ≤ B) (hsq : 1+(H0/a0)^2 ≤ B^2) :
    Real.sqrt (1+(H/a)^2) ≤ B := by
  have rat := div_le_div₀ (hH.trans hH') hH' h0 ha
  have pos : 0 ≤ H/a := div_nonneg hH (h0.le.trans ha)
  have sq := mul_self_le_mul_self pos rat
  apply (Real.sqrt_le_iff).2
  exact ⟨hB,by nlinarith⟩

/-- Four multiple levels certify the first family; levels four and six
also certify the full unit-height strip and a height-two rectangle. -/
theorem solution (d : ℕ) (a H : ℝ) (hH : 0 ≤ H)
    (h : ((d ∣ 8 ∨ d ∣ 12 ∨ d ∣ 18 ∨ d ∣ 30) ∧ (6/7:ℝ) ≤ a ∧ H ≤ 1) ∨
      ((d ∣ 4 ∨ d ∣ 6) ∧ (((1/2:ℝ) ≤ a ∧ H ≤ 1) ∨ ((17/25:ℝ) ≤ a ∧ H ≤ 2)))) :
    GRH.DirichletPeriod.Covers d a H := by
  rcases h with ⟨hd,ha,ht⟩ | ⟨hd,h⟩
  · have rt := root_bound (by norm_num : (0:ℝ) < 6/7) ha hH ht
      (by norm_num : (0:ℝ) ≤ 31/20) (by norm_num)
    have go {Q M : ℕ} (hQ : 2 < Q) (hq : d ∣ Q) (hm : 0 < M)
        (gap : ∀ k : ℕ, 2 ≤ k → k ≤ M → ¬ k.Coprime Q)
        (arith : (((Q.totient:ℝ)/4)*(1+31/20))^7 < ((M:ℝ)+1)^6) : Covers d a H :=
      witness hQ hq hm gap (n:=7) (p:=6) (by decide) (by simpa using ha)
        rt arith
    rcases hd with h8|h12|h18|h30
    · apply go (M:=2) (by decide) h8 (by decide)
      · intro k hk hk'; interval_cases k; decide
      · norm_num [show (8:ℕ).totient=4 by decide]
    · apply go (M:=4) (by decide) h12 (by decide)
      · intro k hk hk'; interval_cases k <;> decide
      · norm_num [show (12:ℕ).totient=4 by decide]
    · apply go (M:=4) (by decide) h18 (by decide)
      · intro k hk hk'; interval_cases k <;> decide
      · norm_num [show (18:ℕ).totient=6 by decide]
    · apply go (M:=6) (by decide) h30 (by decide)
      · intro k hk hk'; interval_cases k <;> decide
      · norm_num [show (30:ℕ).totient=8 by decide]
  · have go {p n : ℕ} {B : ℝ} (hn : 0<n) (hp : (p:ℝ)/n ≤ a)
        (rt : Real.sqrt (1+(H/a)^2) ≤ B) (arith : ((2/4:ℝ)*(1+B))^n < (3:ℝ)^p) :
        Covers d a H := by
      rcases hd with h4|h6
      · refine witness (Q:=4) (M:=2) (by decide) h4 (by decide) ?_ hn hp rt ?_
        · intro k hk hk'; interval_cases k; decide
        · norm_num only [show (4:ℕ).totient=2 by decide,Nat.cast_ofNat,show (2:ℝ)+1=3 by norm_num]
          norm_num at arith
          exact arith
      · refine witness (Q:=6) (M:=2) (by decide) h6 (by decide) ?_ hn hp rt ?_
        · intro k hk hk'; interval_cases k; decide
        · norm_num only [show (6:ℕ).totient=2 by decide,Nat.cast_ofNat,show (2:ℝ)+1=3 by norm_num]
          norm_num at arith
          exact arith
    rcases h with ⟨ha,ht⟩ | ⟨ha,ht⟩
    · apply go (p:=1) (n:=2) (B:=9/4) (by decide) (by simpa using ha) _ (by norm_num)
      exact root_bound (by norm_num : (0:ℝ) < 1/2) ha hH ht (by norm_num) (by norm_num)
    · apply go (p:=2) (n:=3) (B:=25/8) (by decide) (by norm_num; linarith) _ (by norm_num)
      exact root_bound (by norm_num : (0:ℝ) < 17/25) ha hH ht (by norm_num) (by norm_num)

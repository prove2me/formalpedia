-- Prove2me | solution 1 for Erdos287.prime_power_cofactor_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T03:05:03.376817+00:00
-- url     : https://prove2.me/submissions/681e0709-9aec-432e-b036-5990878a7647

import Mathlib
import Theorems.Thm_Erdos287_prime_power_cofactor_certificate

open Finset

set_option autoImplicit false

private theorem no_prime_power_multiple_of_small_cofactors
    {k : ℕ} (hk : 2 ≤ k) {f : ℕ → ℕ}
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ range k, (1 : ℚ) / f i = 1)
    {p e B : ℕ} (hp : Nat.Prime p) (he : 1 ≤ e) (hB : B < p)
    (hmax : f (k - 1) < (B + 1) * p ^ e)
    (hsmall : (∑ j ∈ Icc 1 B, Nat.lcmUpto B / j) < p) :
    ∀ i, i < k → ¬ p ^ e ∣ f i := by
  refine Erdos287.prime_power_cofactor_certificate k hk f hf1 hmono hsum p e hp he
    (Icc 1 B) ?_ ?_ ?_
  · intro j hj
    have ⟨ha, hb⟩ := mem_Icc.mp hj
    exact ⟨ha, fun hd => (hb.trans_lt hB).not_ge (Nat.le_of_dvd ha hd)⟩
  · intro i hi hd
    have hfpos : 0 < f i := by have := hf1 i hi; omega
    have hiM : f i ≤ f (k - 1) := by
      rcases eq_or_lt_of_le (show i ≤ k - 1 by omega) with rfl | hlt
      · rfl
      exact (hmono i (k - 1) hlt (by omega)).le
    have hc := Nat.div_mul_cancel hd
    have hpos : 0 < f i / p ^ e := Nat.pos_of_mul_pos_right (hc ▸ hfpos)
    have hlt : (f i / p ^ e) * p ^ e < (B + 1) * p ^ e := by
      rw [hc]
      exact hiM.trans_lt hmax
    exact mem_Icc.mpr ⟨hpos, Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_right hlt)⟩
  · intro T hT hne hd
    obtain ⟨j, hj⟩ := hne
    have hj' := mem_Icc.mp (hT hj)
    have hjdiv : j ∣ Nat.lcmUpto B := Finset.dvd_lcm (hT hj)
    have hjpos := Nat.div_pos (Nat.le_of_dvd (Nat.lcmUpto_pos _) hjdiv) hj'.1
    have hab := single_le_sum (f := fun j => Nat.lcmUpto B / j) (fun _ _ => Nat.zero_le _) hj
    have hlt : (∑ j ∈ T, Nat.lcmUpto B / j) < p := (sum_le_sum_of_subset hT).trans_lt hsmall
    exact hlt.not_ge (Nat.le_of_dvd (hjpos.trans_le hab) hd)

/-- Prime-power cofactors in a unit-fraction representation satisfy a logarithmic bound. -/
theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (p e i : ℕ) (hp : Nat.Prime p) (he : 1 ≤ e) (hi : i < k) (hd : p ^ e ∣ f i) :
    let B := f (k - 1) / p ^ e
    Real.log p ≤ Real.log B + Chebyshev.psi B := by
  classical
  let M := f (k - 1)
  let B := M / p ^ e
  let L := Nat.lcmUpto B
  change Real.log (p : ℝ) ≤ Real.log (B : ℝ) + Chebyshev.psi (B : ℝ)
  have hpowpos : 0 < p ^ e := pow_pos hp.pos _
  have hiM : f i ≤ M := by
    rcases eq_or_lt_of_le (show i ≤ k - 1 by omega) with rfl | hlt
    · rfl
    exact (hmono i (k - 1) hlt (by omega)).le
  have hB : 0 < B := by
    apply Nat.div_pos _ hpowpos
    exact (Nat.le_of_dvd (by have := hf1 i hi; omega) hd).trans hiM
  have hL : 0 < L := Nat.lcmUpto_pos B
  have hBL : p ≤ B * L := by
    by_contra! hbig
    have hBp : B < p := (Nat.le_mul_of_pos_right B hL).trans_lt hbig
    have hMp : M < (B + 1) * p ^ e :=
      (Nat.div_lt_iff_lt_mul hpowpos).mp (Nat.lt_succ_self B)
    have hsumB : (∑ j ∈ Icc 1 B, L / j) < p := by
      refine lt_of_le_of_lt ?_ hbig
      calc
        _ ≤ ∑ _ ∈ Icc 1 B, L := sum_le_sum fun _ _ => Nat.div_le_self _ _
        _ = B * L := by simp
    exact no_prime_power_multiple_of_small_cofactors hk hf1 hmono hsum hp he hBp hMp hsumB i hi hd
  have hBpR : (0 : ℝ) < B := by exact_mod_cast hB
  have hLpR : (0 : ℝ) < L := by exact_mod_cast hL
  have hupper : Real.log (p : ℝ) ≤ Real.log ((B * L : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hBL)
  rw [Nat.cast_mul, Real.log_mul hBpR.ne' hLpR.ne', ← Chebyshev.psi_eq_log_lcmUpto] at hupper
  exact hupper


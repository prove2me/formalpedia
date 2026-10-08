-- Prove2me | solution 1 for CarryRNG.SWB.expansion_period_eq_orderOf
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:14:45.959599+00:00
-- url     : https://prove2.me/submissions/9e5e4bb0-901b-49d5-a07b-63f34269d304

import Mathlib
import Definitions.Def_CarryRNG_AWC_digit

theorem solution (b m k p : ℕ) (hb : 2 ≤ b) (hm : 1 < m)
    (hk : 0 < k ∧ k < m) (hkm : Nat.Coprime k m) (hbm : Nat.Coprime b m)
    (hp : 0 < p) :
    (∀ j : ℕ, 1 ≤ j → CarryRNG.AWC.digit b m k (j + p) = CarryRNG.AWC.digit b m k j) ↔
      orderOf (b : ZMod m) ∣ p := by
  let R (n : ℕ) := b^n*k % m
  have hm0 : 0 < m := by omega
  have hR (n : ℕ) : R n < m := Nat.mod_lt _ hm0
  have hrec (n : ℕ) : b * R n =
      m * CarryRNG.AWC.digit b m k (n+1) + R (n+1) := by
    have he : (b * R n) % m = R (n+1) := by
      dsimp [R]
      rw [pow_succ]
      simp [Nat.mul_mod, mul_assoc, mul_comm, mul_left_comm]
    have hh := Nat.mod_add_div (b * R n) m
    simp only [CarryRNG.AWC.digit, Nat.add_sub_cancel] 
    rw [← he]
    dsimp [R] at hh ⊢
    omega
  rw [orderOf_dvd_iff_pow_eq_one]
  constructor
  · intro hd
    have he (n : ℕ) : b^n * R p + R n = b^n * R 0 + R (n+p) := by
      induction n with
      | zero => simp [add_comm]
      | succ n ih =>
        have h₁ := hrec n
        have h₂ := hrec (n+p)
        have hdig := hd (n+1) (by omega)
        have hidx : n + p + 1 = n+1+p := by omega
        rw [hidx, hdig] at h₂
        rw [pow_succ]
        have hh := congrArg (fun x : ℕ => b*x) ih
        nlinarith
    have hpow : ∀ n : ℕ, n < b^n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ]; nlinarith
    have hrp : R p = R 0 := by
      have hh := he m
      have hn := hpow m
      have h₁ := hR m
      have h₂ := hR (m+p)
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have : R p + 1 ≤ R 0 := hlt
        nlinarith
      · have : R 0 + 1 ≤ R p := hgt
        nlinarith
    have hz : (b : ZMod m)^p * (k : ZMod m) = (k : ZMod m) := by
      have hh := congrArg (fun x : ℕ => (x : ZMod m)) hrp
      simpa [R, ZMod.natCast_mod] using hh
    exact (ZMod.isUnit_iff_coprime k m).mpr hkm |>.mul_right_cancel (by simpa using hz)
  · intro hz j hj
    have hidx : j+p-1 = (j-1)+p := by omega
    have hh : (b^((j-1)+p)*k : ℕ) % m = (b^(j-1)*k : ℕ) % m := by
      apply (ZMod.natCast_eq_natCast_iff _ _ m).mp
      simp only [Nat.cast_mul, Nat.cast_pow, pow_add, hz, mul_one]
    simp only [CarryRNG.AWC.digit, hidx, hh]

#print axioms solution

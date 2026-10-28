-- Prove2me | solution 1 for Erdos624.short_layer_palette_tail
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T19:36:48.632587+00:00
-- url     : https://prove2.me/submissions/2d482f97-adf9-43e1-b39f-fd70cc5ceeb7

import Mathlib
open Finset

namespace E624R14N
open Finset

theorem cen (s : ℕ) : (2 * s).choose s ^ 2 * (3 * s + 1) ≤ 16 ^ s := by
  rw [← Nat.centralBinom_eq_two_mul_choose]
  induction s with
  | zero => simp
  | succ s ih =>
    have h := Nat.succ_mul_centralBinom_succ s
    set c := Nat.centralBinom s
    set c' := Nat.centralBinom (s + 1)
    have key : (s + 1) ^ 2 * (c' ^ 2 * (3 * (s + 1) + 1)) ≤ (s + 1) ^ 2 * 16 ^ (s + 1) := by
      have e : (s + 1) ^ 2 * (c' ^ 2 * (3 * (s + 1) + 1)) =
          4 * (2 * s + 1) ^ 2 * (3 * s + 4) * c ^ 2 := by
        have : ((s + 1) * c') ^ 2 = (2 * (2 * s + 1) * c) ^ 2 := by rw [h]
        nlinarith [this]
      rw [e, pow_succ]
      have h1 : (2 * s + 1) ^ 2 * (3 * s + 4) ≤ 4 * (s + 1) ^ 2 * (3 * s + 1) := by
        nlinarith
      calc 4 * (2 * s + 1) ^ 2 * (3 * s + 4) * c ^ 2
          = 4 * ((2 * s + 1) ^ 2 * (3 * s + 4)) * c ^ 2 := by ring
        _ ≤ 4 * (4 * (s + 1) ^ 2 * (3 * s + 1)) * c ^ 2 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
        _ = 16 * (s + 1) ^ 2 * (c ^ 2 * (3 * s + 1)) := by ring
        _ ≤ 16 * (s + 1) ^ 2 * 16 ^ s := Nat.mul_le_mul_left _ ih
        _ = (s + 1) ^ 2 * (16 ^ s * 16) := by ring
    exact le_of_mul_le_mul_left key (by positivity)

/-- `Σ_{a ≤ R} C(v,a) · 3^(v-R) ≤ 4^v`. -/
lemma low_sum (v R : ℕ) (hR : R ≤ v) :
    (∑ a ∈ range (R + 1), v.choose a) * 3 ^ (v - R) ≤ 4 ^ v := by
  have h4 : (4 : ℕ) ^ v = ∑ a ∈ range (v + 1), v.choose a * 3 ^ (v - a) := by
    have := (add_pow (1 : ℕ) 3 v)
    rw [show (1 : ℕ) + 3 = 4 by norm_num] at this
    rw [this]
    refine sum_congr rfl fun a _ => by rw [one_pow, one_mul, mul_comm, Nat.cast_id]
  rw [h4, sum_mul]
  calc ∑ a ∈ range (R + 1), v.choose a * 3 ^ (v - R)
      ≤ ∑ a ∈ range (R + 1), v.choose a * 3 ^ (v - a) := by
        refine sum_le_sum fun a ha => ?_
        rw [mem_range] at ha
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    _ ≤ ∑ a ∈ range (v + 1), v.choose a * 3 ^ (v - a) :=
        sum_le_sum_of_subset (range_subset_range.2 (by omega))

lemma exp_ineq (v : ℕ) (hv : 56 ≤ v) : 16 ^ v * 2 ^ 28 < 27 ^ v := by
  induction v, hv using Nat.le_induction with
  | base => norm_num
  | succ v _ ih =>
    rw [pow_succ 16, pow_succ 27]
    have h1 := Nat.mul_lt_mul_of_pos_right ih (show 0 < 16 by norm_num)
    have h2 : 27 ^ v * 16 ≤ 27 ^ v * 27 := Nat.mul_le_mul_left _ (by norm_num)
    calc 16 ^ v * 16 * 2 ^ 28 = 16 ^ v * 2 ^ 28 * 16 := by ring
      _ < 27 ^ v * 16 := h1
      _ ≤ 27 ^ v * 27 := h2

theorem tail (k : ℕ) (hk : 55 ≤ k) :
    64 * ∑ a ∈ range ((k + 1) / 4 + 1), (k + 1).choose a < 2 ^ k := by
  set v := k + 1 with hv
  set R := v / 4 with hR
  set w := v - R with hw
  have h4w : 3 * v ≤ 4 * w := by omega
  have hlow := low_sum v R (by omega)
  -- 2^(v+7) < 3^w
  have hpow : 2 ^ (v + 7) < 3 ^ w := by
    have a1 : (2 ^ (v + 7)) ^ 4 < (3 ^ w) ^ 4 := by
      calc (2 ^ (v + 7)) ^ 4 = 16 ^ v * 2 ^ 28 := by
            rw [← pow_mul, show (v + 7) * 4 = 4 * v + 28 by ring, pow_add, pow_mul]; norm_num
        _ < 27 ^ v := exp_ineq v (by omega)
        _ = 3 ^ (3 * v) := by rw [pow_mul]; norm_num
        _ ≤ 3 ^ (4 * w) := Nat.pow_le_pow_right (by norm_num) h4w
        _ = (3 ^ w) ^ 4 := by rw [← pow_mul, mul_comm]
    exact lt_of_pow_lt_pow_left₀ 4 (by positivity) a1
  set S := ∑ a ∈ range (R + 1), v.choose a
  have : S * 2 ^ (v + 7) < 4 ^ v := by
    rcases Nat.eq_zero_or_pos S with h0 | hpos
    · rw [h0]; simp
    · calc S * 2 ^ (v + 7) < S * 3 ^ w := Nat.mul_lt_mul_of_pos_left hpow hpos
        _ ≤ 4 ^ v := hlow
  have e4 : (4 : ℕ) ^ v = 2 ^ v * 2 ^ v := by rw [← mul_pow]; norm_num
  have e2 : (2 : ℕ) ^ (v + 7) = 2 ^ v * 128 := by rw [pow_add]; norm_num
  have e3 : (2 : ℕ) ^ v = 2 ^ k * 2 := by rw [hv, pow_succ]
  rw [e4, e2] at this
  have h5 : S * 128 < 2 ^ v := by
    have hp : 0 < 2 ^ v := by positivity
    nlinarith
  rw [e3] at h5
  omega
end E624R14N

namespace Erdos624

theorem short_layer_palette_tail (k : ℕ) (hk : 55 ≤ k) :
    64 * ∑ a ∈ range ((k + 1) / 4 + 1), (k + 1).choose a < 2 ^ k := by
  exact E624R14N.tail k hk

end Erdos624

open Finset

theorem solution (k : ℕ) (hk : 55 ≤ k) :
    64 * ∑ a ∈ range ((k + 1) / 4 + 1), (k + 1).choose a < 2 ^ k :=
  Erdos624.short_layer_palette_tail k hk

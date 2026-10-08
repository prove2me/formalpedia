-- Prove2me | solution 1 for BellmanDP.Fibonacci.binet_formula
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:32:16.801371+00:00
-- url     : https://prove2.me/submissions/5db99ef3-f849-4642-b999-947bf928f2b9

import Mathlib
import Definitions.Def_BellmanDP_Fibonacci_SearchModel



namespace BellmanDP.Fibonacci

open SearchTree

lemma bf_ss (n : ℕ) : bookFib (n+2) = bookFib (n+1) + bookFib n := rfl

lemma bf_pos (n : ℕ) : 1 ≤ bookFib n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [bookFib]
    | 1 => simp [bookFib]
    | n+2 => rw [bf_ss]; have := ih (n+1) (by omega); omega

lemma bf_le_succ (n : ℕ) : bookFib n ≤ bookFib (n+1) := by
  cases n with
  | zero => simp [bookFib]
  | succ n => rw [bf_ss]; omega

lemma bf_lt_succ (n : ℕ) (hn : 1 ≤ n) : bookFib n < bookFib (n+1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n-1, by omega⟩
  rw [bf_ss]; have := bf_pos k; omega

lemma bfR_ss (n : ℕ) : (bookFib (n+2) : ℝ) = bookFib (n+1) + bookFib n := by
  rw [bf_ss]; push_cast; ring

lemma bfR_pos (n : ℕ) : (1 : ℝ) ≤ bookFib n := by exact_mod_cast bf_pos n

lemma bfR_le_succ (n : ℕ) : (bookFib n : ℝ) ≤ bookFib (n+1) := by exact_mod_cast bf_le_succ n

lemma bfR_lt_succ (n : ℕ) (hn : 1 ≤ n) : (bookFib n : ℝ) < bookFib (n+1) := by
  exact_mod_cast bf_lt_succ n hn

lemma bfR0 : (bookFib 0 : ℝ) = 1 := by simp [bookFib]
lemma bfR1 : (bookFib 1 : ℝ) = 1 := by simp [bookFib]
lemma bfR2 : (bookFib 2 : ℝ) = 2 := by norm_num [bookFib]


open Filter Topology

lemma ratio_lim (A B r1 r2 : ℝ) (F : ℕ → ℝ) (hF : ∀ n, F n = A * r1 ^ n + B * r2 ^ n)
    (hFpos : ∀ n, 0 < F n) (hA : A ≠ 0) (hr1 : 0 < r1) (hq : |r2| < r1) :
    Tendsto (fun n => F (n+1) / F n) atTop (𝓝 r1) := by
  set q := r2 / r1 with hq_def
  have hr2 : r2 = q * r1 := by rw [hq_def]; field_simp
  have hqa : |q| < 1 := by
    rw [hq_def, abs_div, abs_of_pos hr1, div_lt_one hr1]; exact hq
  have hlim : Tendsto (fun n : ℕ => q ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hqa
  have hT : Tendsto (fun n : ℕ => (A * r1 + B * r2 * q ^ n) / (A + B * q ^ n)) atTop
      (𝓝 ((A * r1 + B * r2 * 0) / (A + B * 0))) :=
    ((hlim.const_mul _).const_add _).div ((hlim.const_mul _).const_add _) (by simpa using hA)
  have hval : (A * r1 + B * r2 * 0) / (A + B * 0) = r1 := by
    simp only [mul_zero, add_zero]; field_simp
  rw [hval] at hT
  refine hT.congr (fun n => ?_)
  have h1 := hFpos n
  have h2 := hFpos (n+1)
  rw [hF n] at h1
  have hden : A + B * q ^ n ≠ 0 := by
    intro h0
    have : A * r1 ^ n + B * r2 ^ n = r1 ^ n * (A + B * q ^ n) := by rw [hr2, mul_pow]; ring
    rw [this, h0, mul_zero] at h1
    exact lt_irrefl _ h1
  rw [hF (n+1), hF n, div_eq_div_iff hden h1.ne', hr2, mul_pow, mul_pow]
  ring

theorem binet_formula_core :
    (∀ n : ℕ, (bookFib n : ℝ) =
      ((1 - Real.sqrt 5) / 2 - 1) / ((1 - Real.sqrt 5) / 2 - (1 + Real.sqrt 5) / 2) *
          ((1 + Real.sqrt 5) / 2) ^ n +
        (1 - (1 + Real.sqrt 5) / 2) / ((1 - Real.sqrt 5) / 2 - (1 + Real.sqrt 5) / 2) *
          ((1 - Real.sqrt 5) / 2) ^ n) ∧
    Tendsto (fun n : ℕ => (bookFib (n + 1) : ℝ) / bookFib n) atTop
      (𝓝 ((1 + Real.sqrt 5) / 2)) := by
  have hs2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : 1 < Real.sqrt 5 := by nlinarith
  generalize Real.sqrt 5 = s at hs2 hs0 hs1 ⊢
  have hne : (1 - s) / 2 - (1 + s) / 2 ≠ 0 := by intro h; linarith
  have q1 : ((1 + s) / 2) ^ 2 = (1 + s) / 2 + 1 := by linear_combination hs2 / 4
  have q2 : ((1 - s) / 2) ^ 2 = (1 - s) / 2 + 1 := by linear_combination hs2 / 4
  have key : ∀ n : ℕ, (bookFib n : ℝ) =
      ((1 - s) / 2 - 1) / ((1 - s) / 2 - (1 + s) / 2) * ((1 + s) / 2) ^ n +
        (1 - (1 + s) / 2) / ((1 - s) / 2 - (1 + s) / 2) * ((1 - s) / 2) ^ n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      match n with
      | 0 =>
        rw [bfR0, pow_zero, pow_zero, mul_one, mul_one, ← add_div,
          show (1 - s) / 2 - 1 + (1 - (1 + s) / 2) = (1 - s) / 2 - (1 + s) / 2 by ring,
          div_self hne]
      | 1 =>
        rw [bfR1, pow_one, pow_one, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
          show ((1 - s) / 2 - 1) * ((1 + s) / 2) + (1 - (1 + s) / 2) * ((1 - s) / 2)
            = (1 - s) / 2 - (1 + s) / 2 by ring, div_self hne]
      | n+2 =>
        rw [bfR_ss, ih (n+1) (by omega), ih n (by omega)]
        have e1 : ((1 + s) / 2) ^ (n+2) = ((1 + s) / 2) ^ (n+1) + ((1 + s) / 2) ^ n := by
          linear_combination ((1 + s) / 2) ^ n * q1
        have e2 : ((1 - s) / 2) ^ (n+2) = ((1 - s) / 2) ^ (n+1) + ((1 - s) / 2) ^ n := by
          linear_combination ((1 - s) / 2) ^ n * q2
        rw [e1, e2]
        ring
  refine ⟨key, ?_⟩
  refine ratio_lim _ _ _ _ (fun n => (bookFib n : ℝ)) key
    (fun n => by have := bfR_pos n; linarith) ?_ (by linarith) ?_
  · intro h
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · linarith
    · exact hne h
  · rw [abs_lt]; constructor <;> linarith

end BellmanDP.Fibonacci

open BellmanDP.Fibonacci
open Filter Topology

theorem solution :
    (∀ n : ℕ, (bookFib n : ℝ) =
      ((1 - Real.sqrt 5) / 2 - 1) / ((1 - Real.sqrt 5) / 2 - (1 + Real.sqrt 5) / 2) *
          ((1 + Real.sqrt 5) / 2) ^ n +
        (1 - (1 + Real.sqrt 5) / 2) / ((1 - Real.sqrt 5) / 2 - (1 + Real.sqrt 5) / 2) *
          ((1 - Real.sqrt 5) / 2) ^ n) ∧
    Tendsto (fun n : ℕ => (bookFib (n + 1) : ℝ) / bookFib n) atTop
      (𝓝 ((1 + Real.sqrt 5) / 2)) := by
  exact binet_formula_core

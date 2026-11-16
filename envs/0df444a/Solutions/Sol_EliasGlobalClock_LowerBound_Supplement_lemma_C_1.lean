-- Prove2me | solution 1 for EliasGlobalClock.LowerBound.Supplement.lemma_C_1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:47:19.595702+00:00
-- url     : https://prove2.me/submissions/83264f66-cfac-4231-be69-1448262bff39

import Mathlib
import Definitions.Def_EliasGlobalClock_LowerBound_Supplement_algorithmTwo

open EliasGlobalClock.LowerBound.Supplement

lemma xexp (y : ℝ) : y * Real.exp (-y) ≤ Real.exp (-1) := by
  have h := Real.add_one_le_exp (y - 1)
  have he : Real.exp (y - 1) = Real.exp y * Real.exp (-1) := by rw [← Real.exp_add]; ring_nf
  have hpos := Real.exp_pos (-y)
  have : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-1)]

lemma x2exp (x : ℝ) (hx : 0 ≤ x) : 3 * (x ^ 2 * Real.exp (-x)) ≤ 2 := by
  have h1 := xexp (x / 2)
  have hy : 0 ≤ x / 2 * Real.exp (-(x / 2)) := by positivity
  have hsq : x ^ 2 * Real.exp (-x) = 4 * (x / 2 * Real.exp (-(x / 2))) ^ 2 := by
    rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
  have he : Real.exp (-1) ^ 2 * Real.exp 1 ^ 2 = 1 := by
    rw [← mul_pow, ← Real.exp_add]; simp
  have he1 : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9
  have hsq2 : (x / 2 * Real.exp (-(x / 2))) ^ 2 ≤ Real.exp (-1) ^ 2 := pow_le_pow_left₀ hy h1 2
  rw [hsq]
  have : Real.exp (-1) ^ 2 ≤ 1 / 7 := by
    have h7 : 7 < Real.exp 1 ^ 2 := by nlinarith
    have := Real.exp_pos (-1)
    nlinarith
  nlinarith

lemma boundA (j : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ((j : ℝ) + 1) * (p * (1 - p) ^ j) ≤ 1 := by
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ p by linarith) j
  have h1 : (1 - p) ^ j * (1 + p) ^ j ≤ 1 := by
    rw [← mul_pow]; apply pow_le_one₀ <;> nlinarith
  have h0 : 0 ≤ (1 - p) ^ j := pow_nonneg (by linarith) j
  have : (1 - p) ^ j * (1 + j * p) ≤ 1 := by nlinarith
  nlinarith

lemma boundB (j : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ((j : ℝ) + 1) * (((j : ℝ) + 2) * p ^ 2 * (1 - p) ^ j) ≤ 2 := by
  rcases Nat.lt_or_ge j 2 with hj | hj
  · interval_cases j
    · simp; rw [abs_of_nonneg hp0]; exact hp1
    · simp
      have h1 : p ^ 2 * (1 - p) ≤ p * (1 - p) := by
        have : p ^ 2 ≤ p := by nlinarith
        exact mul_le_mul_of_nonneg_right this (by linarith)
      have h2 : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
      nlinarith
  · have hjr : (2 : ℝ) ≤ j := by exact_mod_cast hj
    have hexp : (1 - p) ^ j ≤ Real.exp (-(j * p)) := by
      have : (1 - p) ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
      calc (1 - p) ^ j ≤ Real.exp (-p) ^ j := pow_le_pow_left₀ (by linarith) this j
        _ = Real.exp (-(j * p)) := by rw [← Real.exp_nat_mul]; ring_nf
    have hx := x2exp (j * p) (by positivity)
    have hc : ((j : ℝ) + 1) * ((j : ℝ) + 2) ≤ 3 * (j : ℝ) ^ 2 := by nlinarith
    have h0 : 0 ≤ (1 - p) ^ j := pow_nonneg (by linarith) j
    have hp2 : 0 ≤ p ^ 2 := sq_nonneg p
    calc ((j : ℝ) + 1) * (((j : ℝ) + 2) * p ^ 2 * (1 - p) ^ j)
        = ((j : ℝ) + 1) * ((j : ℝ) + 2) * p ^ 2 * (1 - p) ^ j := by ring
      _ ≤ 3 * (j : ℝ) ^ 2 * p ^ 2 * (1 - p) ^ j := by gcongr
      _ ≤ 3 * (j : ℝ) ^ 2 * p ^ 2 * Real.exp (-(j * p)) := by gcongr
      _ = 3 * ((j * p) ^ 2 * Real.exp (-(j * p))) := by ring
      _ ≤ 2 := hx

lemma stepC1 (N k : ℕ) (hNpos : 0 < N) (hk : 1 ≤ k) (hNk : N ≤ 2 * k) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |singletonProb (k + 1) p - singletonProb k p| ≤ 4 / N := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hA := boundA j p hp0 hp1
  have hB := boundB j p hp0 hp1
  have h0 : 0 ≤ (1 - p) ^ j := pow_nonneg (by linarith) j
  have hApos : 0 ≤ p * (1 - p) ^ j := mul_nonneg hp0 h0
  have hBpos : 0 ≤ ((j : ℝ) + 2) * p ^ 2 * (1 - p) ^ j := by positivity
  have hdiff : singletonProb (j + 1 + 1) p - singletonProb (j + 1) p
      = p * (1 - p) ^ j - ((j : ℝ) + 2) * p ^ 2 * (1 - p) ^ j := by
    unfold singletonProb
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  rw [hdiff]
  have hNr : (N : ℝ) ≤ 2 * ((j : ℝ) + 1) := by exact_mod_cast (by omega : N ≤ 2 * (j + 1))
  have hNp : (0 : ℝ) < N := by exact_mod_cast hNpos
  rw [le_div_iff₀ hNp]
  have hAN : p * (1 - p) ^ j * N ≤ 2 := by
    calc p * (1 - p) ^ j * N ≤ p * (1 - p) ^ j * (2 * ((j : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hNr hApos
      _ = 2 * (((j : ℝ) + 1) * (p * (1 - p) ^ j)) := by ring
      _ ≤ 2 := by linarith
  have hBN : ((j : ℝ) + 2) * p ^ 2 * (1 - p) ^ j * N ≤ 4 := by
    calc ((j : ℝ) + 2) * p ^ 2 * (1 - p) ^ j * N
        ≤ ((j : ℝ) + 2) * p ^ 2 * (1 - p) ^ j * (2 * ((j : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hNr hBpos
      _ = 2 * (((j : ℝ) + 1) * (((j : ℝ) + 2) * p ^ 2 * (1 - p) ^ j)) := by ring
      _ ≤ 4 := by linarith
  have hA0 : 0 ≤ p * (1 - p) ^ j * N := mul_nonneg hApos hNp.le
  have hB0 : 0 ≤ ((j : ℝ) + 2) * p ^ 2 * (1 - p) ^ j * N := mul_nonneg hBpos hNp.le
  rcases abs_cases (p * (1 - p) ^ j - ((j : ℝ) + 2) * p ^ 2 * (1 - p) ^ j) with ⟨h, _⟩ | ⟨h, _⟩ <;>
    rw [h] <;> nlinarith

lemma teleC1 (N a : ℕ) (hNpos : 0 < N) (ha : 1 ≤ a) (hNa : N ≤ 2 * a) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ d : ℕ, |singletonProb (a + d) p - singletonProb a p| ≤ d * (4 / N) := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    have hs := stepC1 N (a + d) hNpos (by omega) (by omega) p hp0 hp1
    have htri : |singletonProb (a + (d + 1)) p - singletonProb a p| ≤
        |singletonProb (a + d + 1) p - singletonProb (a + d) p| + |singletonProb (a + d) p - singletonProb a p| := by
      rw [← add_assoc]; exact abs_sub_le _ _ _
    push_cast
    linarith

theorem solution (N n : ℕ) (hN : 2 ≤ N) (hn : 1 ≤ n)
    (hnN : |(n : ℝ) - N| ≤ (N : ℝ) / 2) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |singletonProb n p - singletonProb N p| ≤ 4 * |(n : ℝ) - N| / N := by
  have hNpos : 0 < N := by omega
  rcases le_total n N with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have hd : ((n + d : ℕ) : ℝ) ≤ 2 * n := by
      have := (abs_le.1 hnN).1
      push_cast at this ⊢; linarith
    have hNa : n + d ≤ 2 * n := by exact_mod_cast hd
    have := teleC1 (n + d) n hNpos hn hNa p hp0 hp1 d
    rw [abs_sub_comm] at this
    have habs : |(n : ℝ) - ((n + d : ℕ) : ℝ)| = d := by
      push_cast; rw [show (n : ℝ) - (n + d) = -d by ring, abs_neg, abs_of_nonneg (by positivity)]
    rw [habs]
    calc _ ≤ d * (4 / ((n + d : ℕ) : ℝ)) := this
      _ = _ := by ring
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have := teleC1 N N hNpos (by omega) (by omega) p hp0 hp1 d
    have habs : |((N + d : ℕ) : ℝ) - N| = d := by
      push_cast; rw [show (N : ℝ) + d - N = d by ring, abs_of_nonneg (by positivity)]
    rw [habs]
    calc _ ≤ d * (4 / (N : ℝ)) := this
      _ = _ := by ring

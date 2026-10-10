-- Prove2me | solution 1 for Erdos68.factorial_tail_sharp_window
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-10-10T00:38:02.944022+00:00
-- url     : https://prove2.me/submissions/050e0421-b07b-4694-a006-3f2eff1121de

import Mathlib

open scoped BigOperators

/-!
Direct proof of `Erdos68.factorial_tail_sharp_window`:

    1/(M+1) < M! * ∑' n, 1/((n+M+1)! - 1) < 1/M     (M ≥ 3)

The helper lemmas `e68_fact_sub_one_pos`, `e68_key_le`, `e68_term_nonneg`,
`e68_term_le`, `e68_ratio_lt`, `e68_summable`, `e68_tail_upper`,
`e68_tail_lower`, and the numerical blocks `hFbig`, `hK`, `ht_lo`, `ht_hi`
below are reproduced from the accepted platform reduction of
`Erdos68.irrational_from_tail_bounds`
(submission `054f0b09-45e0-465c-9650-8d089f4cd21f`), where they occur inline.
-/

lemma e68_fact_sub_one_pos {m : ℕ} (hm : 2 ≤ m) : (0 : ℝ) < (m.factorial : ℝ) - 1 := by
  have : 1 < m.factorial := Nat.one_lt_factorial.mpr (by omega)
  have : (1 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast this
  linarith

lemma e68_key_le {s : ℕ} (n : ℕ) (hs : 2 ≤ s) :
    ((s.factorial : ℝ) - 1) * ((s : ℝ) + 1) ^ n ≤ ((n + s).factorial : ℝ) - 1 := by
  have h1 : s.factorial * (s + 1) ^ n ≤ (s + n).factorial :=
    Nat.factorial_mul_pow_le_factorial
  have h1' : (s.factorial : ℝ) * ((s : ℝ) + 1) ^ n ≤ ((n + s).factorial : ℝ) := by
    rw [add_comm n s]; exact_mod_cast h1
  have h2 : (1 : ℝ) ≤ ((s : ℝ) + 1) ^ n :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg s : (0:ℝ) ≤ s)])
  nlinarith

lemma e68_term_nonneg {s : ℕ} (n : ℕ) (hs : 2 ≤ s) :
    0 ≤ 1 / (((n + s).factorial : ℝ) - 1) :=
  le_of_lt (one_div_pos.mpr (e68_fact_sub_one_pos (by omega)))

lemma e68_term_le {s : ℕ} (n : ℕ) (hs : 2 ≤ s) :
    1 / (((n + s).factorial : ℝ) - 1) ≤
      (1 / ((s.factorial : ℝ) - 1)) * (1 / ((s : ℝ) + 1)) ^ n := by
  have hpos : 0 < ((s.factorial : ℝ) - 1) * ((s : ℝ) + 1) ^ n :=
    mul_pos (e68_fact_sub_one_pos hs) (by positivity)
  rw [div_pow, one_pow, one_div_mul_one_div]
  exact one_div_le_one_div_of_le hpos (e68_key_le n hs)

lemma e68_ratio_lt {s : ℕ} (hs : 2 ≤ s) : 1 / ((s : ℝ) + 1) < 1 := by
  rw [div_lt_one (by positivity)]
  have : (2 : ℝ) ≤ s := by exact_mod_cast hs
  linarith

lemma e68_summable {s : ℕ} (hs : 2 ≤ s) :
    Summable (fun n : ℕ => 1 / (((n + s).factorial : ℝ) - 1)) :=
  Summable.of_nonneg_of_le (fun n => e68_term_nonneg n hs) (fun n => e68_term_le n hs)
    ((summable_geometric_of_lt_one (by positivity) (e68_ratio_lt hs)).mul_left _)

lemma e68_tail_upper {s : ℕ} (hs : 2 ≤ s) :
    ∑' n : ℕ, 1 / (((n + s).factorial : ℝ) - 1) ≤
      (1 / ((s.factorial : ℝ) - 1)) * (((s : ℝ) + 1) / s) := by
  have hg := summable_geometric_of_lt_one (by positivity) (e68_ratio_lt hs)
  have hs0 : (s : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  calc ∑' n : ℕ, 1 / (((n + s).factorial : ℝ) - 1)
      ≤ ∑' n : ℕ, (1 / ((s.factorial : ℝ) - 1)) * (1 / ((s : ℝ) + 1)) ^ n :=
        Summable.tsum_le_tsum (fun n => e68_term_le n hs) (e68_summable hs) (hg.mul_left _)
    _ = (1 / ((s.factorial : ℝ) - 1)) * (1 - 1 / ((s : ℝ) + 1))⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) (e68_ratio_lt hs)]
    _ = (1 / ((s.factorial : ℝ) - 1)) * (((s : ℝ) + 1) / s) := by
        congr 1
        have h1 : (s : ℝ) + 1 ≠ 0 := by positivity
        have h : 1 - 1 / ((s : ℝ) + 1) = (s : ℝ) / ((s : ℝ) + 1) := by
          field_simp <;> ring
        rw [h, inv_div]

lemma e68_tail_lower {s : ℕ} (hs : 2 ≤ s) :
    1 / ((s.factorial : ℝ) - 1) ≤ ∑' n : ℕ, 1 / (((n + s).factorial : ℝ) - 1) := by
  have := (e68_summable hs).le_tsum 0 (fun j _ => e68_term_nonneg j hs)
  simpa using this

theorem solution (M : ℕ) (hM : 3 ≤ M) :
    1 / ((M : ℝ) + 1) < (M.factorial : ℝ) * ∑' n : ℕ, (1 : ℝ) / ((n + M + 1).factorial - 1) ∧
    (M.factorial : ℝ) * ∑' n : ℕ, (1 : ℝ) / ((n + M + 1).factorial - 1) < 1 / (M : ℝ) := by
  let F : ℝ := (M.factorial : ℝ)
  have hF : F = (M.factorial : ℝ) := rfl
  let T : ℝ := ∑' n : ℕ, 1 / (((n + (M + 1)).factorial : ℝ) - 1)
  have hT : T = ∑' n : ℕ, 1 / (((n + (M + 1)).factorial : ℝ) - 1) := rfl
  have hTlo := e68_tail_lower (s := M + 1) (by omega)
  have hThi := e68_tail_upper (s := M + 1) (by omega)
  rw [← hT] at hTlo hThi
  -- numerical facts
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hFbig : (M : ℝ) + 1 < F := by
    have hnat : M + 1 < M.factorial := by
      obtain ⟨k, rfl⟩ : ∃ k, M = k + 3 := ⟨M - 3, by omega⟩
      simp only [Nat.factorial_succ]
      have h1 : 1 ≤ k.factorial := Nat.factorial_pos k
      have h3 : 2 * (k + 1) ≤ (k + 1 + 1) * ((k + 1) * k.factorial) :=
        Nat.mul_le_mul (by omega) (by nlinarith)
      have h4 : (k + 2 + 1) * (2 * (k + 1)) ≤ (k + 2 + 1) * ((k + 1 + 1) * ((k + 1) * k.factorial)) :=
        Nat.mul_le_mul_left _ h3
      nlinarith [h4]
    have h' : ((M + 1 : ℕ) : ℝ) < ((M.factorial : ℕ) : ℝ) := Nat.cast_lt.mpr hnat
    push_cast at h'
    linarith [h', hF]
  have hK : (((M + 1).factorial : ℕ) : ℝ) - 1 = ((M : ℝ) + 1) * F - 1 := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hKpos : 0 < ((M : ℝ) + 1) * F - 1 := by nlinarith
  rw [hK] at hTlo hThi
  push_cast at hThi
  let t : ℝ := F * T
  have ht : t = F * T := rfl
  have ht_lo : 1 / ((M : ℝ) + 1) < t := by
    have h1 : F * (1 / (((M : ℝ) + 1) * F - 1)) ≤ t := by
      rw [ht]; exact mul_le_mul_of_nonneg_left hTlo (by linarith)
    have h2 : 1 / ((M : ℝ) + 1) < F * (1 / (((M : ℝ) + 1) * F - 1)) := by
      rw [mul_one_div, div_lt_div_iff₀ (by linarith) hKpos]
      nlinarith
    linarith
  have ht_hi : t < 1 / (M : ℝ) := by
    have h1 : t ≤ F * ((1 / (((M : ℝ) + 1) * F - 1)) * (((M : ℝ) + 1 + 1) / ((M : ℝ) + 1))) := by
      rw [ht]; exact mul_le_mul_of_nonneg_left hThi (by linarith)
    have h2 : F * ((1 / (((M : ℝ) + 1) * F - 1)) * (((M : ℝ) + 1 + 1) / ((M : ℝ) + 1))) <
        1 / (M : ℝ) := by
      have e : F * ((1 / (((M : ℝ) + 1) * F - 1)) * (((M : ℝ) + 1 + 1) / ((M : ℝ) + 1))) =
          (F * ((M : ℝ) + 2)) / ((((M : ℝ) + 1) * F - 1) * ((M : ℝ) + 1)) := by
        field_simp; ring
      rw [e, div_lt_div_iff₀ (by positivity) (by linarith)]
      nlinarith
    linarith
  -- bridge the two tsum spellings and conclude
  have hTbridge : ∑' n : ℕ, (1 : ℝ) / ((n + M + 1).factorial - 1) = T := by
    have cong : (∑' n : ℕ, (1 : ℝ) / ((n + M + 1).factorial - 1)) =
        ∑' n : ℕ, 1 / (((n + (M + 1)).factorial : ℝ) - 1) := by
      apply tsum_congr
      intro n
      have hn : (n + M + 1 : ℕ) = n + (M + 1) := by omega
      have hfac : (n + M + 1).factorial = (n + (M + 1)).factorial := congrArg Nat.factorial hn
      rw [hfac]
    rw [cong]
  rw [hTbridge, ← hF, ← ht]
  exact ⟨ht_lo, ht_hi⟩

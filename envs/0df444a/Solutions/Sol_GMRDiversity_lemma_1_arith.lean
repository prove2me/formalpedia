-- Prove2me | solution 1 for GMRDiversity.lemma_1_arith
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-12T15:22:21.612683+00:00
-- url     : https://prove2.me/submissions/17b39782-945f-4566-8331-c938b94eba2e

import Mathlib

set_option autoImplicit false

/-- Lemma 1 arithmetic: the sum of `2 ^ min w (j-1)` controls both the size of `v` and, when
`v ≥ 2/3`, forces `T` to grow like `2 ^ (n-w)`. -/
theorem solution (n w T : ℕ) (v : ℝ) (hn : 2 ≤ n) (hw : 1 ≤ w) (hwn : w ≤ n)
    (hv : v ≤ (1 + ∑ j ∈ Finset.Icc 1 T, (2 : ℝ) ^ min w (j - 1)) / 2 ^ n) :
    (v ≤ (2 : ℝ) ^ T / 2 ^ n ∧ v ≤ 1 / 2 ^ n + T * 2 ^ w / 2 ^ n) ∧
    (2 / 3 ≤ v → n ≤ T ∧ w ≤ T ∧ (5 / 12 : ℝ) * 2 ^ (n - w) ≤ T) := by
  let S : ℕ → ℝ := fun T => ∑ j ∈ Finset.Icc 1 T, (2 : ℝ) ^ min w (j - 1)
  have hS_succ : ∀ T, S (T + 1) = S T + (2 : ℝ) ^ min w T := by
    intro T
    dsimp only [S]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ T + 1)]
    rw [show T + 1 - 1 = T by omega]
  change v ≤ (1 + S T) / 2 ^ n at hv
  have hF : ∀ T, 1 + S T ≤ (2 : ℝ) ^ T := by
    intro T
    induction T with
    | zero => simp [S]
    | succ T ih =>
        rw [hS_succ]
        have hterm : (2 : ℝ) ^ min w T ≤ (2 : ℝ) ^ T :=
          pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.min_le_right w T)
        have hpow : (2 : ℝ) ^ (T + 1) = (2 : ℝ) ^ T + (2 : ℝ) ^ T := by
          rw [pow_succ]; ring
        linarith
  have hS_le : ∀ T, S T ≤ (T : ℝ) * (2 : ℝ) ^ w := by
    intro T
    induction T with
    | zero => simp [S]
    | succ T ih =>
        rw [hS_succ]
        have hterm : (2 : ℝ) ^ min w T ≤ (2 : ℝ) ^ w :=
          pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.min_le_left w T)
        have hcast : ((T + 1 : ℕ) : ℝ) = (T : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        nlinarith
  have hU : ∀ T, w ≤ T → 1 + S T ≤ (2 : ℝ) ^ w * (((T - w + 1 : ℕ)) : ℝ) := by
    intro T
    induction T with
    | zero =>
        intro h0
        omega
    | succ T ih =>
        intro hT
        rw [hS_succ]
        by_cases hwT : w ≤ T
        · have ih' := ih hwT
          have hmin : min w T = w := Nat.min_eq_left hwT
          rw [hmin]
          have hcast : (((T + 1) - w + 1 : ℕ) : ℝ) = (((T - w + 1 : ℕ)) : ℝ) + 1 := by
            have hz : (T + 1) - w + 1 = (T - w + 1) + 1 := by omega
            rw [hz]; push_cast; ring
          rw [hcast]
          nlinarith
        · push Not at hwT
          have hw_eq : w = T + 1 := by omega
          have hmin : min w T = T := by omega
          rw [hmin, hw_eq]
          have hz : T + 1 - (T + 1) + 1 = 1 := by omega
          rw [hz]
          norm_num
          have ih1 := hF T
          have hpow : (2 : ℝ) ^ (T + 1) = (2 : ℝ) ^ T + (2 : ℝ) ^ T := by
            rw [pow_succ]; ring
          linarith
  have hfirst : v ≤ (2 : ℝ) ^ T / 2 ^ n := by
    calc v ≤ (1 + S T) / 2 ^ n := hv
      _ ≤ (2 : ℝ) ^ T / 2 ^ n := div_le_div_of_nonneg_right (hF T) (by positivity)
  have hsecond : v ≤ 1 / 2 ^ n + T * 2 ^ w / 2 ^ n := by
    have hnum : 1 + S T ≤ 1 + (T : ℝ) * 2 ^ w := by
      have := hS_le T
      linarith
    calc v ≤ (1 + S T) / 2 ^ n := hv
      _ ≤ (1 + (T : ℝ) * 2 ^ w) / 2 ^ n :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ = 1 / 2 ^ n + T * 2 ^ w / 2 ^ n := by ring
  refine ⟨⟨hfirst, hsecond⟩, ?_⟩
  intro hv2
  have hkey : (2 / 3 : ℝ) * 2 ^ n ≤ 1 + S T := by
    have hpos : (0 : ℝ) < 2 ^ n := by positivity
    exact (le_div_iff₀ hpos).mp (hv2.trans hv)
  have hT_ge_n : n ≤ T := by
    have h1 : (2 / 3 : ℝ) * 2 ^ n ≤ (2 : ℝ) ^ T := le_trans hkey (hF T)
    have h2 : (2 : ℝ) ^ (n - 1) < (2 / 3 : ℝ) * 2 ^ n := by
      have hn1 : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
        conv_lhs => rw [show n = n - 1 + 1 by omega]
        rw [pow_succ]
        ring
      rw [hn1]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (n - 1)]
    have h3 : (2 : ℝ) ^ (n - 1) < (2 : ℝ) ^ T := lt_of_lt_of_le h2 h1
    have h4 : n - 1 < T := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h3
    omega
  have hT_ge_w : w ≤ T := le_trans hwn hT_ge_n
  have hfinal : (5 / 12 : ℝ) * 2 ^ (n - w) ≤ T := by
    by_contra hcon
    push Not at hcon
    have hupper := hU T hT_ge_w
    have hTle : (T : ℝ) ≤ (5 / 12 : ℝ) * 2 ^ (n - w) := le_of_lt hcon
    have hstep : (2 : ℝ) ^ w * (((T - w + 1 : ℕ)) : ℝ) ≤
        (2 : ℝ) ^ w * ((5 / 12 : ℝ) * 2 ^ (n - w)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc (((T - w + 1 : ℕ)) : ℝ) ≤ (T : ℝ) := by
            exact_mod_cast (by omega : T - w + 1 ≤ T)
        _ ≤ (5 / 12 : ℝ) * 2 ^ (n - w) := hTle
    have hcontr : (2 / 3 : ℝ) * 2 ^ n ≤ (5 / 12 : ℝ) * 2 ^ n := by
      calc (2 / 3 : ℝ) * 2 ^ n ≤ 1 + S T := hkey
        _ ≤ (2 : ℝ) ^ w * (((T - w + 1 : ℕ)) : ℝ) := hupper
        _ ≤ (2 : ℝ) ^ w * ((5 / 12 : ℝ) * 2 ^ (n - w)) := hstep
        _ = (5 / 12 : ℝ) * 2 ^ n := by
            rw [show (2 : ℝ) ^ n = 2 ^ w * 2 ^ (n - w) by
              rw [← pow_add]
              congr 1
              omega]
            ring
    have hposn : 0 < (2 : ℝ) ^ n := by positivity
    nlinarith
  exact ⟨hT_ge_n, hT_ge_w, hfinal⟩

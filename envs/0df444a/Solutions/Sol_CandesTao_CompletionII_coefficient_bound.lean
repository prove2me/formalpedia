-- Prove2me | solution 1 for CandesTao.CompletionII.coefficient_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T00:48:10.379365+00:00
-- url     : https://prove2.me/submissions/45c9f0c5-c18c-4884-b526-aac551faae45

import Mathlib
import Definitions.Def_CandesTao_CompletionII_CenteredOperators
import Definitions.Def_CandesTao_CompletionII_ExpansionCoefficients

open MatrixCompletion

namespace CB1b52fed6

open CandesTao.CompletionII

/-- integer exponent -/
noncomputable def ex (k j : ℕ) : ℤ := ⌈((k : ℝ) - (j : ℝ)) / 2⌉

lemma ex_succ_shift (k j : ℕ) : ex (k + 1) (j + 1) = ex k j := by
  unfold ex; push_cast; ring_nf

lemma ex_succ_le (k j : ℕ) : ex (k + 1) j ≤ ex k j + 1 := by
  unfold ex
  rw [← Int.ceil_add_one]
  apply Int.ceil_mono
  push_cast; linarith

lemma ex_succ_le' (k j : ℕ) : ex (k + 1) j ≤ ex k (j + 1) + 1 := by
  unfold ex
  rw [← Int.ceil_add_one]
  apply le_of_eq; congr 1
  push_cast; ring

lemma lam_mul_zpow (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (e e' : ℤ) (h : e' ≤ e + 1) :
    lam * lam ^ e ≤ lam ^ e' := by
  rcases h0.eq_or_lt with hz | hlt
  · subst hz; simp; exact zpow_nonneg le_rfl _
  · rw [mul_comm, ← zpow_add_one₀ hlt.ne']
    exact zpow_le_zpow_right_of_le_one₀ hlt h1 h

lemma lin_bd (c u v s lam Y Z : ℝ) (hc : |c| ≤ lam) (hs : |s| ≤ 1) (hu : |u| ≤ Y)
    (hv : |v| ≤ Y) (hY : lam * Y ≤ Z) : |c * (u + s * v)| ≤ 2 * Z := by
  have hY0 : 0 ≤ Y := le_trans (abs_nonneg _) hu
  have h1 : |u + s * v| ≤ 2 * Y := by
    calc |u + s * v| ≤ |u| + |s| * |v| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ Y + 1 * Y := by gcongr
      _ = 2 * Y := by ring
  rw [abs_mul]
  calc |c| * |u + s * v| ≤ lam * (2 * Y) := by
        gcongr; exact le_trans (abs_nonneg _) hc
    _ = 2 * (lam * Y) := by ring
    _ ≤ 2 * Z := by linarith

lemma sum_bd (u v s Y : ℝ) (hs : |s| ≤ 1) (hu : |u| ≤ Y) (hv : |v| ≤ Y) :
    |u + s * v| ≤ 2 * Y := by
  have hY0 : 0 ≤ Y := le_trans (abs_nonneg _) hu
  calc |u + s * v| ≤ |u| + |s| * |v| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ Y + 1 * Y := by gcongr
    _ = 2 * Y := by ring

lemma main (p ρ' lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (ha : |ρ' * (1 - 2 * p) / p| ≤ lam) (hb : |ρ' * (1 - p) / p| ≤ lam)
    (hr : |ρ'| ≤ lam) (hs : |1 - ρ'| ≤ 1) (k : ℕ) :
    ∀ j, |(expansionCoeffs p ρ' k).α j| ≤ lam ^ ex k j * 4 ^ k ∧
      |(expansionCoeffs p ρ' k).β j| ≤ lam ^ ex k j * 4 ^ k ∧
      |(expansionCoeffs p ρ' k).γ j| ≤ lam ^ ex k j * 4 ^ k ∧
      |(expansionCoeffs p ρ' k).δ j| ≤ lam ^ ex k j * 4 ^ k := by
  induction k with
  | zero =>
    intro j
    have hn : (0 : ℝ) ≤ lam ^ ex 0 j := zpow_nonneg hl0 _
    simp only [expansionCoeffs, pow_zero, mul_one, abs_zero]
    refine ⟨?_, hn, hn, hn⟩
    by_cases hj : j = 0
    · subst hj; simp [ex]
    · simp [hj, hn]
  | succ k ih =>
    intro j
    set c := expansionCoeffs p ρ' k with hc
    have hstep : expansionCoeffs p ρ' (k + 1) = c.step p ρ' := rfl
    rw [hstep]
    have hX0 : 0 ≤ lam ^ ex (k + 1) j * 4 ^ k := by positivity
    have h4 : lam ^ ex (k + 1) j * 4 ^ (k + 1) = 4 * (lam ^ ex (k + 1) j * 4 ^ k) := by
      ring
    rw [h4]
    set X := lam ^ ex (k + 1) j * 4 ^ k with hX
    -- the "lambda times" bound
    have hmul : ∀ i, ex (k + 1) j ≤ ex k i + 1 → lam * (lam ^ ex k i * 4 ^ k) ≤ X := by
      intro i hi
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (lam_mul_zpow lam hl0 hl1 _ _ hi) (by positivity)
    have hA := hmul j (ex_succ_le k j)
    have hB := hmul (j + 1) (ex_succ_le' k j)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [ExpansionCoeffs.step]
      rcases j with _ | j
      · simp only [shiftDown, if_true, mul_zero, add_zero, zero_add]
        have h1 := lin_bd _ _ _ _ _ _ _ ha hs (ih 0).1 (ih 0).2.2.1 hA
        have h2 := lin_bd _ _ _ _ _ _ _ hr hs (ih 0).2.1 (ih 0).2.2.2 hA
        calc _ ≤ _ := abs_add_le _ _
          _ ≤ 2 * X + 2 * X := add_le_add h1 h2
          _ = 4 * X := by ring
      · simp only [shiftDown, Nat.add_one_ne_zero, if_false, add_zero, Nat.add_sub_cancel]
        have hsh : lam ^ ex k j * 4 ^ k = X := by rw [hX, ex_succ_shift]
        have h0 := sum_bd _ _ _ _ hs (hsh ▸ (ih j).1) (hsh ▸ (ih j).2.2.1)
        have h1 := lin_bd _ _ _ _ _ _ _ ha hs (ih (j+1)).1 (ih (j+1)).2.2.1 hA
        calc _ ≤ _ := abs_add_le _ _
          _ ≤ 2 * X + 2 * X := add_le_add h0 h1
          _ = 4 * X := by ring
    · simp only [ExpansionCoeffs.step]
      rcases j with _ | j
      · simp only [shiftDown, if_true, lt_irrefl, if_false, mul_zero, add_zero, zero_add]
        have h1 := lin_bd _ _ _ _ _ _ _ hb hs (ih 0).1 (ih 0).2.2.1 hA
        linarith
      · simp only [shiftDown, Nat.add_one_ne_zero, if_false, add_zero, Nat.add_sub_cancel,
          Nat.succ_pos, if_true]
        have hsh : lam ^ ex k j * 4 ^ k = X := by rw [hX, ex_succ_shift]
        have h0 := sum_bd _ _ _ _ hs (hsh ▸ (ih j).2.1) (hsh ▸ (ih j).2.2.2)
        have h1 := lin_bd _ _ _ _ _ _ _ ha hs (ih (j+1)).2.1 (ih (j+1)).2.2.2 hA
        calc _ ≤ _ := abs_add_le _ _
          _ ≤ 2 * X + 2 * X := add_le_add h0 h1
          _ = 4 * X := by ring
    · simp only [ExpansionCoeffs.step]
      have h1 := lin_bd _ _ _ _ _ _ _ hb hs (ih (j+1)).1 (ih (j+1)).2.2.1 hB
      linarith
    · simp only [ExpansionCoeffs.step]
      have h1 := lin_bd _ _ _ _ _ _ _ hb hs (ih (j+1)).2.1 (ih (j+1)).2.2.2 hB
      linarith

end CB1b52fed6

open MatrixCompletion CandesTao.CompletionII in
theorem solution (n r m : ℕ) (hm : 0 < m) (hmn : m ≤ n * n)
    (hI22 : 2 * n * r ≤ m) (k j : ℕ) :
    let p : ℝ := (m : ℝ) / (n : ℝ) ^ 2
    let lam : ℝ := rhoPrime n r / p
    let c := expansionCoeffs p (rhoPrime n r) k
    max (max |c.α j| |c.β j|) (max |c.γ j| |c.δ j|) ≤
      lam ^ ⌈((k : ℝ) - (j : ℝ)) / 2⌉ * 4 ^ k := by
  intro p lam c
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; omega
    · exact h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmnR : (m : ℝ) ≤ (n : ℝ) ^ 2 := by rw [sq]; exact_mod_cast hmn
  have hIR : 2 * (n : ℝ) * r ≤ m := by exact_mod_cast hI22
  have hrR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hp0 : 0 < p := by positivity
  have hp1 : p ≤ 1 := by
    show (m : ℝ) / (n : ℝ) ^ 2 ≤ 1
    rw [div_le_one (by positivity)]; exact hmnR
  set ρ := (r : ℝ) / (n : ℝ) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have h2ρ : 2 * ρ ≤ p := by
    show 2 * ((r : ℝ) / n) ≤ (m : ℝ) / (n : ℝ) ^ 2
    rw [le_div_iff₀ (by positivity)]
    have : 2 * ((r : ℝ) / n) * (n : ℝ) ^ 2 = 2 * n * r := by
      field_simp
    rw [this]; exact hIR
  have hρ' : rhoPrime n r = 2 * ρ - ρ ^ 2 := rfl
  have hr0 : 0 ≤ rhoPrime n r := by rw [hρ']; nlinarith
  have hrp : rhoPrime n r ≤ p := by rw [hρ']; nlinarith
  have hl0 : 0 ≤ lam := div_nonneg hr0 hp0.le
  have hl1 : lam ≤ 1 := by
    show rhoPrime n r / p ≤ 1
    rw [div_le_one hp0]; exact hrp
  have hlam : rhoPrime n r = lam * p := by
    show rhoPrime n r = rhoPrime n r / p * p
    field_simp
  have ha : |rhoPrime n r * (1 - 2 * p) / p| ≤ lam := by
    rw [mul_div_right_comm, abs_mul, abs_of_nonneg hl0]
    have : |1 - 2 * p| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    calc lam * |1 - 2 * p| ≤ lam * 1 := mul_le_mul_of_nonneg_left this hl0
      _ = lam := mul_one _
  have hb : |rhoPrime n r * (1 - p) / p| ≤ lam := by
    rw [mul_div_right_comm, abs_mul, abs_of_nonneg hl0]
    have : |1 - p| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    calc lam * |1 - p| ≤ lam * 1 := mul_le_mul_of_nonneg_left this hl0
      _ = lam := mul_one _
  have hr : |rhoPrime n r| ≤ lam := by
    rw [abs_of_nonneg hr0, hlam]; nlinarith
  have hs : |1 - rhoPrime n r| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith
  have H := CB1b52fed6.main p (rhoPrime n r) lam hl0 hl1 ha hb hr hs k j
  simp only [CB1b52fed6.ex] at H
  obtain ⟨h1, h2, h3, h4⟩ := H
  exact max_le (max_le h1 h2) (max_le h3 h4)

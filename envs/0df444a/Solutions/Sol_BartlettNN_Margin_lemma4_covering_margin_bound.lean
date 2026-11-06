-- Prove2me | solution 1 for BartlettNN.Margin.lemma4_covering_margin_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T11:04:23.710318+00:00
-- url     : https://prove2.me/submissions/326c38fc-85e9-44be-b584-5da5cecc9539

import Mathlib
import Definitions.Def_BartlettNN_Margin_Classification
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_BartlettNN_Margin_Squash
import Definitions.Def_BartlettNN_Margin_Covering

/-! 02146583 BartlettNN.Margin.lemma4_covering_margin_bound: median ghost + swaps + sharp Rademacher tail. -/

/-! C2 of 02146583: binomial median `P(Bin(n,p) ≥ ⌊np⌋) ≥ 1/2` (Kaas-Buhrman 1980).
Proof: pair `u j = b(k+j)` with `v j = b(k-1-j)`; the sign of `u - v` changes at most once
(+ to -), and `∑ (2j+1)(u j - v j) = 2np - 2k + 1 ≥ 0`, so `∑ u ≥ ∑ v`. -/

open Finset

set_option autoImplicit false

namespace B4c2

noncomputable def bb (n : ℕ) (p : ℝ) (x : ℕ) : ℝ := (n.choose x : ℝ) * p ^ x * (1 - p) ^ (n - x)

lemma bb_nonneg (n : ℕ) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (x : ℕ) : 0 ≤ bb n p x := by
  unfold bb
  have : 0 ≤ 1 - p := by linarith
  positivity

lemma bb_eq_zero (n : ℕ) (p : ℝ) {x : ℕ} (hx : n < x) : bb n p x = 0 := by
  unfold bb; rw [Nat.choose_eq_zero_of_lt hx]; simp

lemma bb_succ (n : ℕ) (p : ℝ) {x : ℕ} (hx : x < n) :
    bb n p (x + 1) * ((x : ℝ) + 1) * (1 - p) = bb n p x * ((n : ℝ) - x) * p := by
  obtain ⟨d, rfl⟩ : ∃ d, n = x + 1 + d := ⟨n - (x + 1), by omega⟩
  have h := Nat.choose_succ_right_eq (x + 1 + d) x
  have e1 : x + 1 + d - x = d + 1 := by omega
  have e2 : x + 1 + d - (x + 1) = d := by omega
  rw [e1] at h
  have h' : ((x + 1 + d).choose (x + 1) : ℝ) * ((x : ℝ) + 1)
      = ((x + 1 + d).choose x : ℝ) * ((d : ℝ) + 1) := by exact_mod_cast h
  unfold bb
  rw [e1, e2]
  have hc : (((x + 1 + d : ℕ) : ℝ) - x) = d + 1 := by push_cast; ring
  rw [hc]
  linear_combination (p ^ (x + 1) * (1 - p) ^ (d + 1)) * h'

lemma bb_sum (n : ℕ) (p : ℝ) : ∑ x ∈ range (n + 1), bb n p x = 1 := by
  have h := (add_pow p (1 - p) n).symm
  have e : p + (1 - p) = 1 := by ring
  rw [e, one_pow] at h
  rw [← h]
  apply sum_congr rfl
  intro x _
  unfold bb; ring

lemma bb_mean (n : ℕ) (p : ℝ) : ∑ x ∈ range (n + 1), (x : ℝ) * bb n p x = n * p := by
  have h := congrArg (Polynomial.eval p) (bernsteinPolynomial.sum_smul (R := ℝ) n)
  simp only [Polynomial.eval_finsetSum, bernsteinPolynomial,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_natCast, nsmul_eq_mul] at h
  rw [← h]
  apply sum_congr rfl
  intro x _
  unfold bb; ring

lemma sum_shift (F : ℕ → ℝ) (n k : ℕ) (hk : k ≤ n) (hF : ∀ x, n < x → F x = 0) :
    ∑ j ∈ range (n + 1), F (k + j) = ∑ x ∈ Ico k (n + 1), F x := by
  rw [sum_Ico_eq_sum_range]
  refine (sum_subset (by intro j; simp only [mem_range]; omega) ?_).symm
  intro j _ hj
  simp only [mem_range] at hj
  exact hF _ (by omega)

lemma sum_reflect (F : ℕ → ℝ) (n k : ℕ) (hk : k ≤ n + 1) :
    ∑ j ∈ range (n + 1), (if j < k then F (k - 1 - j) else 0) = ∑ x ∈ range k, F x := by
  rw [← sum_range_reflect F k]
  rw [← sum_subset (s₁ := range k) (by intro j; simp only [mem_range]; omega)]
  · apply sum_congr rfl
    intro j hj
    rw [mem_range] at hj
    rw [if_pos hj]
  · intro j _ hj
    rw [mem_range] at hj
    rw [if_neg hj]

lemma weighted (N J : ℕ) (hJ : 1 ≤ J) (f : ℕ → ℝ) (h1 : ∀ j, j < J → j < N → 0 ≤ f j)
    (h2 : ∀ j, J ≤ j → j < N → f j ≤ 0)
    (hw : 0 ≤ ∑ j ∈ range N, (2 * (j : ℝ) + 1) * f j) : 0 ≤ ∑ j ∈ range N, f j := by
  have hle : ∑ j ∈ range N, (2 * (j : ℝ) + 1) * f j ≤ ∑ j ∈ range N, (2 * (J : ℝ)) * f j := by
    apply sum_le_sum
    intro j hj
    rw [mem_range] at hj
    by_cases hjJ : j < J
    · have h := h1 j hjJ hj
      have : (j : ℝ) + 1 ≤ J := by exact_mod_cast hjJ
      nlinarith
    · have h := h2 j (by omega) hj
      have : (J : ℝ) ≤ j := by exact_mod_cast (not_lt.mp hjJ)
      nlinarith
  rw [← mul_sum] at hle
  have hJ' : (0 : ℝ) < 2 * J := by
    have : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    linarith
  by_contra hneg
  push Not at hneg
  have : 2 * (J : ℝ) * ∑ j ∈ range N, f j < 0 := mul_neg_of_pos_of_neg hJ' hneg
  linarith

/-- The step condition `D t`: the ratio `r t / r (t-1)` is `< 1`. -/
def D (n k : ℕ) (p t : ℝ) : Prop :=
  (((n : ℝ) - k + 1) ^ 2 - t ^ 2) * p ^ 2 < ((k : ℝ) ^ 2 - t ^ 2) * (1 - p) ^ 2

lemma D_mono (n k : ℕ) (p t : ℝ) (hp : 1 / 2 ≤ p) (ht : 0 ≤ t) (h : D n k p t) :
    D n k p (t + 1) := by
  unfold D at *
  have h1 : 0 ≤ (2 * t + 1) * (p ^ 2 - (1 - p) ^ 2) := by
    apply mul_nonneg (by linarith)
    nlinarith
  nlinarith

lemma not_D_case1 (n k : ℕ) (p t : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hk1 : 1 ≤ k)
    (hkB : 2 * k ≤ n) (hkn : (k : ℝ) ≤ n * p) (ht0 : 0 ≤ t) (ht : t ≤ (k : ℝ) - 1) :
    ¬ D n k p t := by
  unfold D
  push Not
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hB : 2 * (k : ℝ) ≤ n := by exact_mod_cast hkB
  have hpB : (k : ℝ) * (1 - p) ≤ p * ((n : ℝ) - k) := by nlinarith
  by_cases hpq : p < 1 - p
  · have h1 : ((k : ℝ) * (1 - p)) ^ 2 ≤ (p * ((n : ℝ) - k)) ^ 2 := by
      apply pow_le_pow_left₀ (by nlinarith) hpB
    have h2 : (p * ((n : ℝ) - k)) ^ 2 ≤ (p * ((n : ℝ) - k + 1)) ^ 2 := by
      apply pow_le_pow_left₀ (by nlinarith) (by nlinarith)
    have h3 : t ^ 2 * p ^ 2 ≤ t ^ 2 * (1 - p) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply pow_le_pow_left₀ (by linarith) (by linarith)
    nlinarith
  · push Not at hpq
    have ht2 : t ^ 2 ≤ ((k : ℝ) - 1) ^ 2 := by
      apply pow_le_pow_left₀ ht0 ht
    have hpq2 : (1 - p) ^ 2 ≤ p ^ 2 := by
      apply pow_le_pow_left₀ (by linarith) hpq
    have hA : (k : ℝ) + 1 ≤ (n : ℝ) - k + 1 := by linarith
    have hA2 : ((k : ℝ) + 1) ^ 2 ≤ ((n : ℝ) - k + 1) ^ 2 := by
      apply pow_le_pow_left₀ (by linarith) hA
    have e1 : t ^ 2 * (p ^ 2 - (1 - p) ^ 2) ≤ ((k : ℝ) - 1) ^ 2 * (p ^ 2 - (1 - p) ^ 2) := by
      apply mul_le_mul_of_nonneg_right ht2 (by linarith)
    have e2 : ((k : ℝ) + 1) ^ 2 * p ^ 2 ≤ ((n : ℝ) - k + 1) ^ 2 * p ^ 2 := by
      apply mul_le_mul_of_nonneg_right hA2 (by positivity)
    nlinarith

set_option maxHeartbeats 1000000 in
theorem median_ge (n k : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hk1 : 1 ≤ k)
    (hkn : (k : ℝ) ≤ n * p) :
    ∑ x ∈ range k, bb n p x ≤ ∑ x ∈ Ico k (n + 1), bb n p x := by
  have hkn' : k < n := by
    have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hnp : (0 : ℝ) < n * p := by linarith
    have hn : (0 : ℝ) < n := by nlinarith
    have : (k : ℝ) < n := by nlinarith [mul_pos hn (sub_pos.2 hp1)]
    exact_mod_cast this
  have hq : 0 < 1 - p := by linarith
  set u : ℕ → ℝ := fun j => bb n p (k + j) with hu
  set v : ℕ → ℝ := fun j => if j < k then bb n p (k - 1 - j) else 0 with hv
  have hu0 : ∀ j, 0 ≤ u j := fun j => bb_nonneg n hp0.le hp1.le _
  have hv0 : ∀ j, 0 ≤ v j := by
    intro j; simp only [hv]; split_ifs
    · exact bb_nonneg n hp0.le hp1.le _
    · exact le_refl _
  have Ru : ∀ j, k + j < n →
      u (j + 1) * ((k : ℝ) + j + 1) * (1 - p) = u j * ((n : ℝ) - k - j) * p := by
    intro j hj
    have h := bb_succ n p hj
    push_cast at h
    simp only [hu]
    rw [show k + (j + 1) = k + j + 1 by omega]
    linear_combination h
  have Rv : ∀ j, j + 1 < k →
      v j * ((k : ℝ) - 1 - j) * (1 - p) = v (j + 1) * ((n : ℝ) - k + 2 + j) * p := by
    intro j hj
    obtain ⟨c, hc⟩ : ∃ c, k = j + 2 + c := ⟨k - (j + 2), by omega⟩
    have hcn : c < n := by omega
    have h := bb_succ n p hcn
    simp only [hv, if_pos (show j < k by omega), if_pos hj]
    rw [show k - 1 - j = c + 1 by omega, show k - 1 - (j + 1) = c by omega]
    subst hc
    push_cast
    linear_combination h
  -- mode: u 0 ≥ v 0
  have hmode : v 0 ≤ u 0 := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have h := bb_succ n p (show k' < n by omega)
    simp only [hv, hu, if_pos (show 0 < k' + 1 by omega)]
    rw [show k' + 1 - 1 - 0 = k' by omega, show k' + 1 + 0 = k' + 1 by omega]
    push_cast at hkn
    have hb := bb_nonneg n hp0.le hp1.le k'
    have hkq : 0 < ((k' : ℝ) + 1) * (1 - p) := by positivity
    have : bb n p k' * (((k' : ℝ) + 1) * (1 - p)) ≤ bb n p (k' + 1) * (((k' : ℝ) + 1) * (1 - p)) := by
      have e : bb n p (k' + 1) * (((k' : ℝ) + 1) * (1 - p)) = bb n p k' * ((n : ℝ) - k') * p := by
        linear_combination h
      rw [e]
      have : ((k' : ℝ) + 1) * (1 - p) ≤ ((n : ℝ) - k') * p := by nlinarith
      nlinarith
    exact le_of_mul_le_mul_right this hkq
  -- base: from u i ≥ v i and ¬ D (i+1) get u (i+1) ≥ v (i+1)
  have base : ∀ i, k + i < n → i + 1 < k → v i ≤ u i → ¬ D n k p ((i : ℝ) + 1) →
      v (i + 1) ≤ u (i + 1) := by
    intro i hi1 hi2 hvu hD
    unfold D at hD
    push Not at hD
    have h1 := Ru i hi1
    have h2 := Rv i hi2
    have hi1' : (k : ℝ) + i + 1 ≤ n := by exact_mod_cast hi1
    have hi2' : (i : ℝ) + 2 ≤ k := by exact_mod_cast hi2
    have hZ : 0 < ((k : ℝ) + i + 1) * (1 - p) * (((n : ℝ) - k + 2 + i) * p) := by
      have : 0 < (n : ℝ) - k + 2 + i := by linarith
      positivity
    have eX : u (i + 1) * (((k : ℝ) + i + 1) * (1 - p) * (((n : ℝ) - k + 2 + i) * p))
        = u i * ((((n : ℝ) - k + 1) ^ 2 - ((i : ℝ) + 1) ^ 2) * p ^ 2) := by
      linear_combination (((n : ℝ) - k + 2 + i) * p) * h1
    have eY : v (i + 1) * (((k : ℝ) + i + 1) * (1 - p) * (((n : ℝ) - k + 2 + i) * p))
        = v i * (((k : ℝ) ^ 2 - ((i : ℝ) + 1) ^ 2) * (1 - p) ^ 2) := by
      linear_combination (-((k : ℝ) + i + 1) * (1 - p)) * h2
    have hY : 0 ≤ ((k : ℝ) ^ 2 - ((i : ℝ) + 1) ^ 2) * (1 - p) ^ 2 := by
      apply mul_nonneg _ (by positivity)
      nlinarith
    have hvi := hv0 i
    have : v (i + 1) * (((k : ℝ) + i + 1) * (1 - p) * (((n : ℝ) - k + 2 + i) * p))
        ≤ u (i + 1) * (((k : ℝ) + i + 1) * (1 - p) * (((n : ℝ) - k + 2 + i) * p)) := by
      rw [eX, eY]
      calc v i * (((k : ℝ) ^ 2 - ((i : ℝ) + 1) ^ 2) * (1 - p) ^ 2)
          ≤ v i * ((((n : ℝ) - k + 1) ^ 2 - ((i : ℝ) + 1) ^ 2) * p ^ 2) :=
            mul_le_mul_of_nonneg_left hD hvi
        _ ≤ u i * ((((n : ℝ) - k + 1) ^ 2 - ((i : ℝ) + 1) ^ 2) * p ^ 2) :=
            mul_le_mul_of_nonneg_right hvu (le_trans hY hD)
    exact le_of_mul_le_mul_right this hZ
  -- step: from u i < v i and D (i+1) get u (i+1) < v (i+1)
  have step : ∀ i, k + i < n → i + 1 < k → u i < v i → D n k p ((i : ℝ) + 1) →
      u (i + 1) < v (i + 1) := by
    intro i hi1 hi2 huv hD
    unfold D at hD
    have h1 := Ru i hi1
    have h2 := Rv i hi2
    have hi1' : (k : ℝ) + i + 1 ≤ n := by exact_mod_cast hi1
    have hZ : 0 < ((k : ℝ) + i + 1) * (1 - p) * (((n : ℝ) - k + 2 + i) * p) := by
      have : 0 < (n : ℝ) - k + 2 + i := by linarith
      positivity
    have eX : u (i + 1) * (((k : ℝ) + i + 1) * (1 - p) * (((n : ℝ) - k + 2 + i) * p))
        = u i * ((((n : ℝ) - k + 1) ^ 2 - ((i : ℝ) + 1) ^ 2) * p ^ 2) := by
      linear_combination (((n : ℝ) - k + 2 + i) * p) * h1
    have eY : v (i + 1) * (((k : ℝ) + i + 1) * (1 - p) * (((n : ℝ) - k + 2 + i) * p))
        = v i * (((k : ℝ) ^ 2 - ((i : ℝ) + 1) ^ 2) * (1 - p) ^ 2) := by
      linear_combination (-((k : ℝ) + i + 1) * (1 - p)) * h2
    have hX : 0 ≤ (((n : ℝ) - k + 1) ^ 2 - ((i : ℝ) + 1) ^ 2) * p ^ 2 := by
      apply mul_nonneg _ (by positivity)
      nlinarith
    have hui := hu0 i
    have hvpos : 0 < v i := lt_of_le_of_lt hui huv
    have : u (i + 1) * (((k : ℝ) + i + 1) * (1 - p) * (((n : ℝ) - k + 2 + i) * p))
        < v (i + 1) * (((k : ℝ) + i + 1) * (1 - p) * (((n : ℝ) - k + 2 + i) * p)) := by
      rw [eX, eY]
      calc u i * ((((n : ℝ) - k + 1) ^ 2 - ((i : ℝ) + 1) ^ 2) * p ^ 2)
          ≤ v i * ((((n : ℝ) - k + 1) ^ 2 - ((i : ℝ) + 1) ^ 2) * p ^ 2) :=
            mul_le_mul_of_nonneg_right huv.le hX
        _ < v i * (((k : ℝ) ^ 2 - ((i : ℝ) + 1) ^ 2) * (1 - p) ^ 2) :=
            mul_lt_mul_of_pos_left hD hvpos
    exact lt_of_mul_lt_mul_right this hZ.le
  -- crossing
  have cross : ∃ J, 1 ≤ J ∧ (∀ j, j < J → j < n + 1 → v j ≤ u j) ∧
      (∀ j, J ≤ j → j < n + 1 → u j ≤ v j) := by
    by_cases hex : ∃ j, j < n + 1 ∧ u j < v j
    · classical
      let J0 := Nat.find hex
      have hJ0 : J0 < n + 1 ∧ u J0 < v J0 := Nat.find_spec hex
      have hmin : ∀ j, j < J0 → v j ≤ u j := by
        intro j hj
        have := Nat.find_min hex hj
        push Not at this
        exact this (by omega)
      have hJ0pos : 1 ≤ J0 := by
        by_contra h0
        have : J0 = 0 := by omega
        rw [this] at hJ0
        linarith [hJ0.2, hmode]
      have hJ0k : J0 < k := by
        by_contra hk
        have : v J0 = 0 := by simp only [hv]; rw [if_neg hk]
        linarith [hJ0.2, hu0 J0]
      refine ⟨J0, hJ0pos, fun j hj _ => hmin j hj, ?_⟩
      obtain ⟨i, hi⟩ : ∃ i, J0 = i + 1 := ⟨J0 - 1, by omega⟩
      have hviu : v i ≤ u i := hmin i (by omega)
      by_cases hin : k + i < n
      · have hDJ : D n k p ((i : ℝ) + 1) := by
          by_contra hD
          have := base i hin (by omega) hviu hD
          rw [← hi] at this
          linarith [hJ0.2]
        by_cases hcase : 2 * k ≤ n
        · exfalso
          refine not_D_case1 n k p ((i : ℝ) + 1) hp0 hp1 hk1 hcase hkn (by positivity) ?_ hDJ
          have : ((i + 1 : ℕ) : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
          push_cast [show 1 ≤ k from hk1] at this
          linarith
        · push Not at hcase
          have hp2 : 1 / 2 ≤ p := by
            have : (n : ℝ) < 2 * k := by exact_mod_cast hcase
            nlinarith
          -- induction along the tail
          have ind : ∀ d, k + J0 + d ≤ n → u (J0 + d) < v (J0 + d) ∧ D n k p ((J0 : ℝ) + d) := by
            intro d
            induction d with
            | zero =>
              intro _
              refine ⟨by simpa using hJ0.2, ?_⟩
              rw [hi]; push_cast; simpa using hDJ
            | succ d ih =>
              intro hd
              obtain ⟨h1, h2⟩ := ih (by omega)
              have hD' : D n k p (((J0 + d : ℕ) : ℝ) + 1) := by
                have := D_mono n k p ((J0 : ℝ) + d) hp2 (by positivity) h2
                push_cast; exact this
              refine ⟨?_, ?_⟩
              · have := step (J0 + d) (by omega) (by omega) h1 hD'
                simpa [Nat.add_assoc] using this
              · push_cast at hD' ⊢
                rw [show (J0 : ℝ) + (d + 1) = J0 + d + 1 by ring]
                exact hD'
          intro j hj hjn
          by_cases hjB : k + j ≤ n
          · have := (ind (j - J0) (by omega)).1
            rw [show J0 + (j - J0) = j by omega] at this
            exact this.le
          · have : u j = 0 := by simp only [hu]; exact bb_eq_zero n p (by omega)
            rw [this]; exact hv0 j
      · intro j hj _
        have : u j = 0 := by simp only [hu]; exact bb_eq_zero n p (by omega)
        rw [this]; exact hv0 j
    · push Not at hex
      exact ⟨n + 1, by omega, fun j _ hj => hex j hj, fun j hj hj' => absurd hj' (by omega)⟩
  -- weighted identity
  have hsumu : ∑ j ∈ range (n + 1), u j = ∑ x ∈ Ico k (n + 1), bb n p x :=
    sum_shift (bb n p) n k hkn'.le (fun x hx => bb_eq_zero n p hx)
  have hsumv : ∑ j ∈ range (n + 1), v j = ∑ x ∈ range k, bb n p x :=
    sum_reflect (bb n p) n k (by omega)
  have hwu : ∑ j ∈ range (n + 1), (2 * (j : ℝ) + 1) * u j
      = ∑ x ∈ Ico k (n + 1), (2 * (x : ℝ) - 2 * k + 1) * bb n p x := by
    rw [← sum_shift (fun x => (2 * (x : ℝ) - 2 * k + 1) * bb n p x) n k hkn'.le
      (fun x hx => by simp [bb_eq_zero n p hx])]
    apply sum_congr rfl
    intro j _
    simp only [hu]
    push_cast; ring
  have hwv : ∑ j ∈ range (n + 1), (2 * (j : ℝ) + 1) * v j
      = ∑ x ∈ range k, (2 * (k : ℝ) - 2 * x - 1) * bb n p x := by
    rw [← sum_reflect (fun x => (2 * (k : ℝ) - 2 * x - 1) * bb n p x) n k (by omega)]
    apply sum_congr rfl
    intro j _
    simp only [hv]
    split_ifs with hjk
    · have : ((k - 1 - j : ℕ) : ℝ) = (k : ℝ) - 1 - j := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      rw [this]; ring
    · ring
  have htot : ∑ x ∈ range (n + 1), (2 * (x : ℝ) - 2 * k + 1) * bb n p x
      = 2 * (n * p) - 2 * k + 1 := by
    have e : ∀ x ∈ range (n + 1), (2 * (x : ℝ) - 2 * k + 1) * bb n p x
        = 2 * ((x : ℝ) * bb n p x) - (2 * k - 1) * bb n p x := by
      intro x _; ring
    rw [sum_congr rfl e, sum_sub_distrib, ← mul_sum, ← mul_sum, bb_mean, bb_sum]
    ring
  have hsplit := sum_range_add_sum_Ico (fun x => (2 * (x : ℝ) - 2 * k + 1) * bb n p x)
    (show k ≤ n + 1 by omega)
  have hneg : ∑ x ∈ range k, (2 * (k : ℝ) - 2 * x - 1) * bb n p x
      = -∑ x ∈ range k, (2 * (x : ℝ) - 2 * k + 1) * bb n p x := by
    rw [← sum_neg_distrib]; apply sum_congr rfl; intro x _; ring
  have hW : 0 ≤ ∑ j ∈ range (n + 1), (2 * (j : ℝ) + 1) * (u j - v j) := by
    have e : ∑ j ∈ range (n + 1), (2 * (j : ℝ) + 1) * (u j - v j)
        = ∑ j ∈ range (n + 1), (2 * (j : ℝ) + 1) * u j
          - ∑ j ∈ range (n + 1), (2 * (j : ℝ) + 1) * v j := by
      rw [← sum_sub_distrib]; apply sum_congr rfl; intro j _; ring
    rw [e, hwu, hwv, hneg]
    have : 2 * (n * p) - 2 * (k : ℝ) + 1 ≥ 0 := by linarith
    linarith
  obtain ⟨J, hJ1, hJa, hJb⟩ := cross
  have := weighted (n + 1) J hJ1 (fun j => u j - v j)
    (fun j hj hjn => by have := hJa j hj hjn; linarith)
    (fun j hj hjn => by have := hJb j hj hjn; linarith) hW
  rw [sum_sub_distrib, hsumu, hsumv] at this
  linarith

theorem binomial_floor_median (m : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 : ℝ) / 2 ≤ ∑ k ∈ Finset.Icc ⌊(m : ℝ) * p⌋₊ m,
      (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) := by
  set k := ⌊(m : ℝ) * p⌋₊ with hk
  have hkm : k ≤ m := by
    apply Nat.floor_le_of_le
    nlinarith [show (0 : ℝ) ≤ m from by positivity]
  have hIcc : Finset.Icc k m = Finset.Ico k (m + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have e : ∑ x ∈ Finset.Icc k m, (m.choose x : ℝ) * p ^ x * (1 - p) ^ (m - x)
      = ∑ x ∈ Ico k (m + 1), bb m p x := by
    rw [hIcc]; rfl
  rw [e]
  have htot : ∑ x ∈ range k, bb m p x + ∑ x ∈ Ico k (m + 1), bb m p x = 1 := by
    rw [sum_range_add_sum_Ico _ (show k ≤ m + 1 by omega), bb_sum]
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · rw [hk0, sum_range_zero] at htot
    rw [hk0]; linarith
  rcases eq_or_lt_of_le hp1 with hp1' | hp1'
  · have hz : ∑ x ∈ range k, bb m p x = 0 := by
      apply sum_eq_zero
      intro x hx
      rw [mem_range] at hx
      unfold bb
      rw [hp1', sub_self, zero_pow (by omega)]
      ring
    linarith
  · have hp0' : 0 < p := by
      rcases eq_or_lt_of_le hp0 with h | h
      · exfalso
        rw [← h, mul_zero, Nat.floor_zero] at hk
        omega
      · exact h
    have hkn : (k : ℝ) ≤ m * p := Nat.floor_le (by positivity)
    have := median_ge m k p hp0' hp1' hk0 hkn
    linarith

end B4c2


/-! C1 of 02146583: sharp Rademacher tail with the floor threshold.
Key fact (d): for `c ∈ {-1,0,1}^m` with `k = #{c i ≠ 0} ≥ 3` and `1 ≤ s ≤ k-1`,
`P(∑ ±c_i ≥ s) ≤ exp(-(s+1)^2/(2k))`, proved by induction on `m`: `H k s = exp(-(s+1)^2/(2k))`
is a supersolution of the discrete heat equation for `(s+1)^2 ≤ k(k+1)` (cosh ≤ exp(x^2/2)),
with boundary values `P(S ≥ 1) ≤ 1/2` (symmetry) and `P(S ≥ k-1) ≤ 2^-k`. -/

open Finset

set_option autoImplicit false

namespace B4c1

def sgnSum {m : ℕ} (c : Fin m → ℤ) (σ : Fin m → Bool) : ℤ := ∑ i, if σ i then c i else -c i

def kk {m : ℕ} (c : Fin m → ℤ) : ℕ := (univ.filter fun i => c i ≠ 0).card

noncomputable def Q {m : ℕ} (c : Fin m → ℤ) (s : ℤ) : ℝ :=
  (∑ σ : Fin m → Bool, if s ≤ sgnSum c σ then (1 : ℝ) else 0) / 2 ^ m

noncomputable def H (k : ℕ) (s : ℤ) : ℝ := Real.exp (-(((s : ℝ) + 1) ^ 2) / (2 * k))

lemma sum_one_pi (m : ℕ) : ∑ _σ : Fin m → Bool, (1 : ℝ) = 2 ^ m := by
  simp

lemma Q_nonneg {m : ℕ} (c : Fin m → ℤ) (s : ℤ) : 0 ≤ Q c s := by
  unfold Q
  apply div_nonneg _ (by positivity)
  apply sum_nonneg; intro σ _; split_ifs <;> norm_num

lemma Q_le_one {m : ℕ} (c : Fin m → ℤ) (s : ℤ) : Q c s ≤ 1 := by
  unfold Q
  rw [div_le_one (by positivity), ← sum_one_pi m]
  apply sum_le_sum; intro σ _; split_ifs <;> norm_num

lemma sgnSum_cons {m : ℕ} (c : Fin (m + 1) → ℤ) (b : Bool) (τ : Fin m → Bool) :
    sgnSum c (Fin.cons b τ) = (if b then c 0 else -c 0) + sgnSum (Fin.tail c) τ := by
  unfold sgnSum
  rw [Fin.sum_univ_succ]
  simp [Fin.tail]

lemma Q_succ {m : ℕ} (c : Fin (m + 1) → ℤ) (s : ℤ) :
    Q c s = (Q (Fin.tail c) (s - c 0) + Q (Fin.tail c) (s + c 0)) / 2 := by
  unfold Q
  rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Bool)).sum_comp, Fintype.sum_prod_type,
    Fintype.sum_bool]
  have e : ∀ (b : Bool) (τ : Fin m → Bool),
      (Fin.consEquiv (fun _ : Fin (m + 1) => Bool)) (b, τ) = Fin.cons b τ := fun _ _ => rfl
  simp only [e, sgnSum_cons, if_true, Bool.false_eq_true, if_false]
  have h1 : ∀ τ : Fin m → Bool, (s ≤ c 0 + sgnSum (Fin.tail c) τ) ↔
      (s - c 0 ≤ sgnSum (Fin.tail c) τ) := fun τ => by constructor <;> intro h <;> linarith
  have h2 : ∀ τ : Fin m → Bool, (s ≤ -c 0 + sgnSum (Fin.tail c) τ) ↔
      (s + c 0 ≤ sgnSum (Fin.tail c) τ) := fun τ => by constructor <;> intro h <;> linarith
  simp only [h1, h2]
  rw [pow_succ]
  field_simp

lemma kk_succ {m : ℕ} (c : Fin (m + 1) → ℤ) :
    kk c = kk (Fin.tail c) + if c 0 = 0 then 0 else 1 := by
  unfold kk
  rw [card_filter, card_filter, Fin.sum_univ_succ]
  by_cases h : c 0 = 0
  · simp [h, Fin.tail]
    apply Finset.sum_congr rfl; intro i _; by_cases h' : c i.succ = 0 <;> simp [h']
  · simp [h, Fin.tail, add_comm]
    apply Finset.sum_congr rfl; intro i _; by_cases h' : c i.succ = 0 <;> simp [h']

lemma sgnSum_le_kk {m : ℕ} (c : Fin m → ℤ) (hc : ∀ i, |c i| ≤ 1) (σ : Fin m → Bool) :
    sgnSum c σ ≤ kk c := by
  unfold sgnSum kk
  rw [card_filter]
  push_cast
  apply sum_le_sum
  intro i _
  have := abs_le.mp (hc i)
  split_ifs <;> omega

/-- (a) above the number of active coordinates the tail is empty. -/
lemma Q_eq_zero {m : ℕ} (c : Fin m → ℤ) (hc : ∀ i, |c i| ≤ 1) (s : ℤ) (hs : (kk c : ℤ) < s) :
    Q c s = 0 := by
  unfold Q
  rw [sum_eq_zero]
  · simp
  intro σ _
  rw [if_neg]
  have := sgnSum_le_kk c hc σ
  omega

lemma Q_succ_zero {m : ℕ} (c : Fin (m + 1) → ℤ) (s : ℤ) (h0 : c 0 = 0) :
    Q c s = Q (Fin.tail c) s := by
  rw [Q_succ, h0]; simp

lemma Q_succ_ne {m : ℕ} (c : Fin (m + 1) → ℤ) (hc : ∀ i, |c i| ≤ 1) (s : ℤ) (h0 : c 0 ≠ 0) :
    Q c s = (Q (Fin.tail c) (s - 1) + Q (Fin.tail c) (s + 1)) / 2 := by
  rw [Q_succ]
  have := abs_le.mp (hc 0)
  rcases (show c 0 = 1 ∨ c 0 = -1 by omega) with h | h
  · rw [h]
  · rw [h]; simp only [sub_neg_eq_add, ← sub_eq_add_neg]; ring

lemma tail_bound {m : ℕ} (c : Fin (m + 1) → ℤ) (hc : ∀ i, |c i| ≤ 1) :
    ∀ i, |Fin.tail c i| ≤ 1 := by
  intro i; exact hc _

/-- (b) at the top the tail is at most `2^-k`. -/
lemma Q_top : ∀ (m : ℕ) (c : Fin m → ℤ), (∀ i, |c i| ≤ 1) → ∀ s : ℤ, (kk c : ℤ) - 1 ≤ s →
    Q c s ≤ (1 / 2 : ℝ) ^ kk c := by
  intro m
  induction m with
  | zero =>
    intro c _ s _
    have : kk c = 0 := by unfold kk; simp
    rw [this, pow_zero]; exact Q_le_one c s
  | succ m ih =>
    intro c hc s hs
    have hk := kk_succ c
    by_cases h0 : c 0 = 0
    · rw [Q_succ_zero c s h0]
      rw [if_pos h0, add_zero] at hk
      rw [hk] at hs ⊢
      exact ih _ (tail_bound c hc) s hs
    · rw [Q_succ_ne c hc s h0]
      rw [if_neg h0] at hk
      rw [hk] at hs ⊢
      push_cast at hs
      have hz : Q (Fin.tail c) (s + 1) = 0 :=
        Q_eq_zero _ (tail_bound c hc) _ (by omega)
      have h1 := ih _ (tail_bound c hc) (s - 1) (by omega)
      rw [hz, pow_succ]
      linarith

/-- (c) symmetry: `P(S ≥ 1) ≤ 1/2`. -/
lemma Q_one {m : ℕ} (c : Fin m → ℤ) : Q c 1 ≤ 1 / 2 := by
  let e : (Fin m → Bool) ≃ (Fin m → Bool) :=
    { toFun := fun σ i => !σ i, invFun := fun σ i => !σ i,
      left_inv := fun σ => by funext i; simp, right_inv := fun σ => by funext i; simp }
  have hneg' : ∀ σ : Fin m → Bool, sgnSum c (fun i => !σ i) = -sgnSum c σ := by
    intro σ
    unfold sgnSum
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    cases h : σ i <;> simp [h]
  have hneg : ∀ σ, sgnSum c (e σ) = -sgnSum c σ := fun σ => hneg' σ
  have hsum : ∑ σ : Fin m → Bool, (if (1 : ℤ) ≤ sgnSum c σ then (1 : ℝ) else 0)
      = ∑ σ : Fin m → Bool, (if (1 : ℤ) ≤ sgnSum c (e σ) then (1 : ℝ) else 0) :=
    (e.sum_comp (fun σ => if (1 : ℤ) ≤ sgnSum c σ then (1 : ℝ) else 0)).symm
  have hle : ∑ σ : Fin m → Bool, ((if (1 : ℤ) ≤ sgnSum c σ then (1 : ℝ) else 0)
      + (if (1 : ℤ) ≤ sgnSum c (e σ) then (1 : ℝ) else 0)) ≤ ∑ _σ : Fin m → Bool, (1 : ℝ) := by
    apply sum_le_sum
    intro σ _
    rw [hneg]
    split_ifs with h1 h2 <;> first | (exfalso; omega) | norm_num
  rw [sum_add_distrib, ← hsum, sum_one_pi] at hle
  unfold Q
  rw [div_le_iff₀ (by positivity)]
  linarith

/-! Real-analysis inputs. -/

lemma half_pow_eq (k : ℕ) : (1 / 2 : ℝ) ^ k = Real.exp (-(k * Real.log 2)) := by
  rw [← Real.exp_log (by positivity : (0 : ℝ) < (1 / 2) ^ k), Real.log_pow, one_div,
    Real.log_inv]
  ring_nf

lemma supersol (k t : ℝ) (hk : 0 < k) (ht : t ^ 2 ≤ k * (k + 1)) :
    (Real.exp (-(t - 1) ^ 2 / (2 * k)) + Real.exp (-(t + 1) ^ 2 / (2 * k))) / 2
      ≤ Real.exp (-t ^ 2 / (2 * (k + 1))) := by
  have e1 : -(t - 1) ^ 2 / (2 * k) = -(t ^ 2 + 1) / (2 * k) + t / k := by field_simp; ring
  have e2 : -(t + 1) ^ 2 / (2 * k) = -(t ^ 2 + 1) / (2 * k) + -(t / k) := by field_simp; ring
  rw [e1, e2, Real.exp_add, Real.exp_add]
  have hc : (Real.exp (-(t ^ 2 + 1) / (2 * k)) * Real.exp (t / k)
      + Real.exp (-(t ^ 2 + 1) / (2 * k)) * Real.exp (-(t / k))) / 2
      = Real.exp (-(t ^ 2 + 1) / (2 * k)) * Real.cosh (t / k) := by
    rw [Real.cosh_eq]; ring
  rw [hc]
  calc Real.exp (-(t ^ 2 + 1) / (2 * k)) * Real.cosh (t / k)
      ≤ Real.exp (-(t ^ 2 + 1) / (2 * k)) * Real.exp ((t / k) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (Real.cosh_le_exp_half_sq _) (Real.exp_pos _).le
    _ = Real.exp (-(t ^ 2 + 1) / (2 * k) + (t / k) ^ 2 / 2) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-t ^ 2 / (2 * (k + 1))) := by
        apply Real.exp_le_exp.mpr
        have : -t ^ 2 / (2 * (k + 1)) - (-(t ^ 2 + 1) / (2 * k) + (t / k) ^ 2 / 2)
            = (k * (k + 1) - t ^ 2) / (2 * k ^ 2 * (k + 1)) := by field_simp; ring
        have : 0 ≤ (k * (k + 1) - t ^ 2) / (2 * k ^ 2 * (k + 1)) :=
          div_nonneg (by linarith) (by positivity)
        linarith

lemma exp_le_pow (x : ℝ) (n : ℕ) (hn : 0 < n) (hx : x < n) :
    Real.exp x ≤ (1 / (1 - x / n)) ^ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : 0 < 1 - x / n := by rw [sub_pos, div_lt_one hn']; exact hx
  have h1 : Real.exp (x / n) ≤ 1 / (1 - x / n) := by
    have := Real.add_one_le_exp (-(x / n))
    rw [Real.exp_neg] at this
    rw [le_div_iff₀ hpos]
    have hep := Real.exp_pos (x / n)
    calc Real.exp (x / n) * (1 - x / n) ≤ Real.exp (x / n) * (Real.exp (x / n))⁻¹ :=
          mul_le_mul_of_nonneg_left (by linarith) hep.le
      _ = 1 := mul_inv_cancel₀ hep.ne'
  calc Real.exp x = Real.exp (x / n) ^ n := by
        rw [← Real.exp_nat_mul]; congr 1; field_simp
    _ ≤ (1 / (1 - x / n)) ^ n := pow_le_pow_left₀ (Real.exp_pos _).le h1 n

lemma pow_le_exp (x : ℝ) (n : ℕ) (hn : 0 < n) (hx : 0 ≤ x) :
    (1 + x / n) ^ n ≤ Real.exp x := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  calc (1 + x / n) ^ n ≤ Real.exp (x / n) ^ n := by
        apply pow_le_pow_left₀ (by positivity)
        have := Real.add_one_le_exp (x / n); linarith
    _ = Real.exp x := by rw [← Real.exp_nat_mul]; congr 1; field_simp

lemma exp_neg_le_of (x : ℝ) (n : ℕ) (hn : 0 < n) (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 / (1 + x / n) ^ n := by
  rw [Real.exp_neg, ← one_div]
  apply one_div_le_one_div_of_le (by positivity) (pow_le_exp x n hn hx)

lemma le_exp_neg_of (x : ℝ) (n : ℕ) (hn : 0 < n) (hx : x < n) :
    1 / (1 / (1 - x / n)) ^ n ≤ Real.exp (-x) := by
  rw [Real.exp_neg, ← one_div]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : 0 < 1 - x / n := by rw [sub_pos, div_lt_one hn']; exact hx
  apply one_div_le_one_div_of_le (Real.exp_pos _) (exp_le_pow x n hn hx)

lemma N3 : (5 / 16 : ℝ) ≤ Real.exp (-(9 / 8)) := by
  have := le_exp_neg_of (9 / 8) 32 (by norm_num) (by norm_num)
  refine le_trans ?_ this
  norm_num

lemma N4 : (Real.exp (-(9 / 8)) + 1 / 16) / 2 ≤ Real.exp (-(8 / 5)) := by
  have h1 := exp_neg_le_of (9 / 8) 128 (by norm_num) (by norm_num)
  have h2 := le_exp_neg_of (8 / 5) 128 (by norm_num) (by norm_num)
  have h3 : (1 / (1 + (9 / 8 : ℝ) / (128 : ℕ)) ^ 128 + 1 / 16) / 2
      ≤ 1 / (1 / (1 - (8 / 5 : ℝ) / (128 : ℕ))) ^ 128 := by norm_num
  linarith

lemma N5 : (Real.exp (-(8 / 5)) + 1 / 32) / 2 ≤ Real.exp (-(25 / 12)) := by
  have h1 := exp_neg_le_of (8 / 5) 128 (by norm_num) (by norm_num)
  have h2 := le_exp_neg_of (25 / 12) 128 (by norm_num) (by norm_num)
  have h3 : (1 / (1 + (8 / 5 : ℝ) / (128 : ℕ)) ^ 128 + 1 / 32) / 2
      ≤ 1 / (1 / (1 - (25 / 12 : ℝ) / (128 : ℕ))) ^ 128 := by norm_num
  linarith

lemma log2_gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9

lemma L1 (k : ℕ) (hk : 3 ≤ k) : (1 / 2 : ℝ) ≤ H k 1 := by
  unfold H
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have : (1 / 2 : ℝ) = Real.exp (-(Real.log 2)) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  rw [this]
  apply Real.exp_le_exp.mpr
  have := log2_gt
  rw [neg_div, neg_le_neg_iff, div_le_iff₀ (by positivity)]
  push_cast
  nlinarith

lemma L2 (k : ℕ) (hk : 1 ≤ k) : (1 / 2 : ℝ) ^ k ≤ H k ((k : ℤ) - 1) := by
  unfold H
  rw [half_pow_eq]
  apply Real.exp_le_exp.mpr
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have := log2_gt
  push_cast
  have e : -(((k : ℝ) - 1 + 1) ^ 2) / (2 * k) = -(k / 2) := by field_simp; ring
  rw [e]
  nlinarith

lemma L5 (k : ℕ) (hk : 6 ≤ k) : (1 / 2 : ℝ) ^ k ≤ H k k := by
  unfold H
  rw [half_pow_eq]
  apply Real.exp_le_exp.mpr
  have hk' : (6 : ℝ) ≤ k := by exact_mod_cast hk
  have := log2_gt
  push_cast
  rw [neg_div, neg_le_neg_iff, div_le_iff₀ (by positivity)]
  have h1 : (k : ℝ) * k * 0.6931471803 ≤ k * k * Real.log 2 :=
    mul_le_mul_of_nonneg_left this.le (by positivity)
  nlinarith [h1, mul_self_nonneg ((k : ℝ) - 6), hk']

set_option maxHeartbeats 1000000 in
/-- (d) the main tail bound. -/
theorem Q_main : ∀ (m : ℕ) (c : Fin m → ℤ), (∀ i, |c i| ≤ 1) → 3 ≤ kk c → ∀ s : ℤ, 1 ≤ s →
    s ≤ (kk c : ℤ) - 1 → Q c s ≤ H (kk c) s := by
  intro m
  induction m with
  | zero =>
    intro c _ hk
    have : kk c = 0 := by unfold kk; simp
    omega
  | succ m ih =>
    intro c hc hk3 s hs1 hs2
    have hk := kk_succ c
    have hct := tail_bound c hc
    by_cases h0 : c 0 = 0
    · rw [Q_succ_zero c s h0]
      rw [if_pos h0, add_zero] at hk
      rw [hk] at hk3 hs2 ⊢
      exact ih _ hct hk3 s hs1 hs2
    · rw [if_neg h0] at hk
      -- boundary s = 1
      by_cases hs1' : s = 1
      · rw [hs1']
        exact le_trans (Q_one c) (L1 _ hk3)
      -- boundary s = k - 1
      by_cases hsk : s = (kk c : ℤ) - 1
      · rw [hsk]
        exact le_trans (Q_top _ c hc _ le_rfl) (L2 _ (by omega))
      rw [Q_succ_ne c hc s h0]
      set k' := kk (Fin.tail c) with hk'
      rw [hk]
      rw [hk] at hs2 hsk
      push_cast at hs2 hsk
      have hk'3 : 3 ≤ k' := by omega
      have hA : Q (Fin.tail c) (s - 1) ≤ H k' (s - 1) :=
        ih _ hct hk'3 (s - 1) (by omega) (by omega)
      have hkpos : (0 : ℝ) < k' := by exact_mod_cast (show 0 < k' by omega)
      have hsR : (2 : ℝ) ≤ s := by exact_mod_cast (show (2 : ℤ) ≤ s by omega)
      have hsk' : (s : ℝ) + 1 ≤ k' := by exact_mod_cast (show s + 1 ≤ (k' : ℤ) by omega)
      have hsup := supersol (k' : ℝ) ((s : ℝ) + 1) hkpos (by nlinarith)
      have eA : H k' (s - 1) = Real.exp (-((s : ℝ) + 1 - 1) ^ 2 / (2 * k')) := by
        unfold H; push_cast; ring_nf
      have eB : H k' (s + 1) = Real.exp (-((s : ℝ) + 1 + 1) ^ 2 / (2 * k')) := by
        unfold H; push_cast; ring_nf
      have eC : H (k' + 1) s = Real.exp (-((s : ℝ) + 1) ^ 2 / (2 * ((k' : ℝ) + 1))) := by
        unfold H; push_cast; ring_nf
      rw [eC]
      by_cases hin : s + 1 ≤ (k' : ℤ) - 1
      · have hB : Q (Fin.tail c) (s + 1) ≤ H k' (s + 1) :=
          ih _ hct hk'3 (s + 1) (by omega) hin
        rw [eA] at hA; rw [eB] at hB
        linarith
      · have hsk2 : s + 1 = (k' : ℤ) := by omega
        have hB : Q (Fin.tail c) (s + 1) ≤ (1 / 2 : ℝ) ^ k' :=
          Q_top _ _ hct (s + 1) (by omega)
        by_cases hk6 : 6 ≤ k'
        · have h5 := L5 k' hk6
          have : H k' (k' : ℤ) = H k' (s + 1) := by rw [hsk2]
          have e5 : H k' (k' : ℤ) = Real.exp (-((s : ℝ) + 1 + 1) ^ 2 / (2 * k')) := by
            rw [this, eB]
          rw [e5] at h5; rw [eA] at hA
          linarith
        · -- k' ∈ {3,4,5}
          have hk'v : k' = 3 ∨ k' = 4 ∨ k' = 5 := by omega
          rcases hk'v with h | h | h
          · have hs2v : s = 2 := by rw [h] at hsk2; push_cast at hsk2; omega
            subst hs2v
            have hQ1 := Q_one (Fin.tail c)
            rw [h] at hB
            have := N3
            rw [h]; push_cast
            norm_num at hQ1 hB this ⊢
            linarith
          · have hs2v : s = 3 := by rw [h] at hsk2; push_cast at hsk2; omega
            subst hs2v
            rw [eA, h] at hA; rw [h] at hB
            have := N4
            rw [h]; norm_num at hA hB this ⊢
            linarith
          · have hs2v : s = 4 := by rw [h] at hsk2; push_cast at hsk2; omega
            subst hs2v
            rw [eA, h] at hA; rw [h] at hB
            have := N5
            rw [h]; norm_num at hA hB this ⊢
            linarith


/-- C1: sharp Rademacher tail with the floor threshold. -/
theorem rademacher_tail_floor (m : ℕ) (hm : 4 ≤ m) (c : Fin m → ℤ) (hc : ∀ i, |c i| ≤ 1)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hεm : 2 * Real.log 4 < m * ε ^ 2) :
    ((Finset.univ.filter fun σ : Fin m → Bool =>
        (⌊(m : ℝ) * ε⌋ : ℤ) ≤ ∑ i, (if σ i then c i else -c i)).card : ℝ) / 2 ^ m
      ≤ Real.exp (-((m : ℝ) * ε ^ 2 / 2)) := by
  set s := ⌊(m : ℝ) * ε⌋ with hs
  have hQ : ((Finset.univ.filter fun σ : Fin m → Bool =>
        s ≤ ∑ i, (if σ i then c i else -c i)).card : ℝ) / 2 ^ m = Q c s := by
    unfold Q sgnSum
    rw [card_filter]
    push_cast
    rfl
  rw [hQ]
  have hmR : (4 : ℝ) ≤ m := by exact_mod_cast hm
  set x := (m : ℝ) * ε with hx
  have hx_le : x ≤ m := by nlinarith
  have hxpos : 0 < x := by positivity
  have hs_le : (s : ℝ) ≤ x := Int.floor_le x
  have hs_lt : x < s + 1 := Int.lt_floor_add_one x
  have eT : -((m : ℝ) * ε ^ 2 / 2) = -(x ^ 2 / (2 * m)) := by
    rw [hx]; field_simp
  rw [eT]
  have hlog2 := log2_gt
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hx2 : 2 * m * Real.log 4 < x ^ 2 := by
    have : x ^ 2 = m * (m * ε ^ 2) := by rw [hx]; ring
    rw [this]
    have hm0 : (0 : ℝ) < m := by linarith
    nlinarith
  have hx3 : 3 < x := by
    rw [hlog4] at hx2
    nlinarith
  have hs3 : (3 : ℤ) ≤ s := by
    rw [hs]; apply Int.le_floor.mpr; push_cast; linarith
  have hkm : kk c ≤ m := by
    unfold kk
    calc (univ.filter fun i => c i ≠ 0).card ≤ (univ : Finset (Fin m)).card := card_filter_le _ _
      _ = m := by simp
  have hkmR : (kk c : ℝ) ≤ m := by exact_mod_cast hkm
  rcases lt_trichotomy s (kk c : ℤ) with h | h | h
  · have hk3 : 3 ≤ kk c := by omega
    refine le_trans (Q_main m c hc hk3 s (by omega) (by omega)) ?_
    unfold H
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_le_neg_iff]
    have hkpos : (0 : ℝ) < kk c := by exact_mod_cast (show 0 < kk c by omega)
    have hsx : x ^ 2 ≤ ((s : ℝ) + 1) ^ 2 := by nlinarith
    calc x ^ 2 / (2 * m) ≤ ((s : ℝ) + 1) ^ 2 / (2 * m) :=
          div_le_div_of_nonneg_right hsx (by positivity)
      _ ≤ ((s : ℝ) + 1) ^ 2 / (2 * kk c) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  · refine le_trans (Q_top m c hc s (by omega)) ?_
    rw [half_pow_eq]
    apply Real.exp_le_exp.mpr
    have hk3 : (3 : ℝ) ≤ kk c := by
      have : (3 : ℤ) ≤ kk c := by omega
      exact_mod_cast this
    have hxk : x < kk c + 1 := by
      have : (s : ℝ) = kk c := by rw [h]; push_cast; ring
      linarith
    have hm0 : (0 : ℝ) < m := by linarith
    rw [neg_le_neg_iff, div_le_iff₀ (by positivity)]
    by_cases hkm' : (kk c : ℝ) + 1 ≤ m
    · have h1 : x ^ 2 ≤ ((kk c : ℝ) + 1) * m := by nlinarith
      have h2 : (kk c : ℝ) + 1 ≤ 2 * kk c * Real.log 2 := by nlinarith
      nlinarith
    · have hmk : m ≤ kk c := by
        have : (m : ℝ) < kk c + 1 := by linarith
        have : m < kk c + 1 := by exact_mod_cast this
        omega
      have hmkR : (m : ℝ) = kk c := by exact_mod_cast le_antisymm hmk hkm
      have h1 : x ^ 2 ≤ (m : ℝ) * m := by nlinarith
      rw [← hmkR]
      nlinarith
  · rw [Q_eq_zero c hc s h]
    exact (Real.exp_pos _).le

end B4c1


/-! C3, C4, C5 of 02146583: product-measure plumbing. -/

open MeasureTheory Finset

set_option autoImplicit false

namespace B4c345

set_option maxHeartbeats 1000000 in
open Classical in
/-- C3: the count of coordinates in `E` under a product measure is binomial. -/
theorem pi_count_ge_eq {Y : Type*} [MeasurableSpace Y] (Q : Measure Y) [IsProbabilityMeasure Q]
    (E : Set Y) (hE : MeasurableSet E) (m j : ℕ) :
    Measure.pi (fun _ : Fin m => Q) {w | j ≤ (Finset.univ.filter fun i => w i ∈ E).card}
      = ENNReal.ofReal (∑ k ∈ Finset.Icc j m,
          (m.choose k : ℝ) * (Q.real E) ^ k * (1 - Q.real E) ^ (m - k)) := by
  set q := Q.real E with hq
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hq1 : q ≤ 1 := by rw [hq]; exact measureReal_le_one
  let piece : Finset (Fin m) → Set (Fin m → Y) :=
    fun S => Set.pi Set.univ (fun i => if i ∈ S then E else Eᶜ)
  have hpiece_meas : ∀ S, MeasurableSet (piece S) := by
    intro S
    apply MeasurableSet.univ_pi
    intro i
    split_ifs
    · exact hE
    · exact hE.compl
  have hmem : ∀ S w, w ∈ piece S ↔ (Finset.univ.filter fun i => w i ∈ E) = S := by
    intro S w
    simp only [piece, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h
      ext i
      have := h i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs at this with hi
      · exact ⟨fun _ => hi, fun _ => this⟩
      · exact ⟨fun h' => absurd h' this, fun h' => absurd h' hi⟩
    · intro h i
      have := congrArg (fun T => i ∈ T) h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
      split_ifs with hi
      · exact this.mpr hi
      · exact fun h' => hi (this.mp h')
  have hset : {w : Fin m → Y | j ≤ (Finset.univ.filter fun i => w i ∈ E).card}
      = ⋃ S ∈ ((Finset.univ : Finset (Fin m)).powerset.filter fun S => j ≤ S.card), piece S := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_powerset,
      exists_prop]
    constructor
    · intro h
      exact ⟨_, ⟨Finset.subset_univ _, h⟩, (hmem _ w).mpr rfl⟩
    · rintro ⟨S, ⟨_, hS⟩, hw⟩
      rw [(hmem S w).mp hw]; exact hS
  have hdisj : Set.PairwiseDisjoint
      (↑((Finset.univ : Finset (Fin m)).powerset.filter fun S => j ≤ S.card)) piece := by
    intro S _ T _ hST
    rw [Function.onFun, Set.disjoint_left]
    intro w hS hT
    exact hST (((hmem S w).mp hS).symm.trans ((hmem T w).mp hT))
  have hpiece : ∀ S : Finset (Fin m), Measure.pi (fun _ : Fin m => Q) (piece S)
      = ENNReal.ofReal (q ^ S.card * (1 - q) ^ (m - S.card)) := by
    intro S
    simp only [piece]
    rw [Measure.pi_pi]
    have e1 : ∀ i, Q (if i ∈ S then E else Eᶜ)
        = if i ∈ S then ENNReal.ofReal q else ENNReal.ofReal (1 - q) := by
      intro i
      split_ifs
      · rw [hq, ofReal_measureReal (measure_ne_top _ _)]
      · rw [← probReal_compl_eq_one_sub hE, ofReal_measureReal (measure_ne_top _ _)]
    simp only [e1]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    have c1 : (Finset.univ.filter fun i => i ∈ S).card = S.card := by
      congr 1; ext i; simp
    have c2 : (Finset.univ.filter fun i => i ∉ S).card = m - S.card := by
      rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), c1]
      simp
    rw [c1, c2, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hq0,
      ENNReal.ofReal_pow (by linarith)]
  rw [hset, measure_biUnion_finset hdisj (fun S _ => hpiece_meas S)]
  simp only [hpiece]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun S _ => by
    have : 0 ≤ 1 - q := by linarith
    positivity)]
  congr 1
  rw [Finset.sum_filter]
  have hcard := Finset.sum_powerset_apply_card
    (fun k => if j ≤ k then q ^ k * (1 - q) ^ (m - k) else 0) (x := (Finset.univ : Finset (Fin m)))
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  rw [show (∑ S ∈ (Finset.univ : Finset (Fin m)).powerset,
      if j ≤ S.card then q ^ S.card * (1 - q) ^ (m - S.card) else 0)
      = ∑ S ∈ (Finset.univ : Finset (Fin m)).powerset,
      (fun k => if j ≤ k then q ^ k * (1 - q) ^ (m - k) else 0) S.card from rfl, hcard]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (m + 1)) (fun k => j ≤ k)]
  have hz : ∑ k ∈ (Finset.range (m + 1)).filter (fun k => ¬ j ≤ k),
      (m.choose k) • (if j ≤ k then q ^ k * (1 - q) ^ (m - k) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [if_neg hk.2, smul_zero]
  rw [hz, add_zero]
  have hI : (Finset.range (m + 1)).filter (fun k => j ≤ k) = Finset.Icc j m := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega
  rw [hI]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Icc] at hk
  rw [if_pos hk.1, nsmul_eq_mul]
  ring

/-- `Fin.append` is measure preserving from the product of two `m`-fold products. -/
lemma measurePreserving_append {Y : Type*} [MeasurableSpace Y] (Q : Measure Y)
    [IsProbabilityMeasure Q] (m : ℕ) :
    MeasurePreserving (fun p : (Fin m → Y) × (Fin m → Y) => Fin.append p.1 p.2)
      ((Measure.pi fun _ : Fin m => Q).prod (Measure.pi fun _ : Fin m => Q))
      (Measure.pi fun _ : Fin (m + m) => Q) := by
  have h1 := measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin m ⊕ Fin m => Q)
  have h2 := measurePreserving_arrowCongr' (fun _ : Fin m ⊕ Fin m => Q)
    (fun _ : Fin (m + m) => Q) finSumFinEquiv (MeasurableEquiv.refl Y)
    (fun _ => MeasurePreserving.id Q)
  convert h2.comp h1 using 1
  funext p
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Equiv.arrowCongr,
      MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi, -Fin.natAdd_eq_addNat]
  · simp [MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Equiv.arrowCongr,
      MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi, -Fin.natAdd_eq_addNat]

/-- C4: ghost-sample symmetrization (first `m` coordinates = `z`, last `m` = ghost). -/
theorem ghost_symmetrization {Y : Type*} [MeasurableSpace Y] (Q : Measure Y)
    [IsProbabilityMeasure Q] (m : ℕ) (A : Set (Fin m → Y)) (hA : MeasurableSet A)
    (J : Set (Fin (m + m) → Y)) (hJ : MeasurableSet J)
    (hgh : ∀ z ∈ A, (1 : ENNReal) / 2 ≤
      Measure.pi (fun _ : Fin m => Q) {z' | Fin.append z z' ∈ J}) :
    Measure.pi (fun _ : Fin m => Q) A ≤ 2 * Measure.pi (fun _ : Fin (m + m) => Q) J := by
  set μ := Measure.pi (fun _ : Fin m => Q) with hμ
  have hΦ := measurePreserving_append Q m
  rw [← hΦ.measure_preimage hJ.nullMeasurableSet, Measure.prod_apply (hΦ.measurable hJ)]
  have hlow : ∫⁻ z, A.indicator (fun _ => (1 : ENNReal) / 2) z ∂μ
      ≤ ∫⁻ z, μ (Prod.mk z ⁻¹' ((fun p : (Fin m → Y) × (Fin m → Y) =>
          Fin.append p.1 p.2) ⁻¹' J)) ∂μ := by
    apply lintegral_mono
    intro z
    by_cases hz : z ∈ A
    · rw [Set.indicator_of_mem hz]
      exact hgh z hz
    · rw [Set.indicator_of_notMem hz]
      exact bot_le
  rw [lintegral_indicator_const hA] at hlow
  calc μ A = 2 * ((1 : ENNReal) / 2 * μ A) := by
        rw [← mul_assoc, ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    _ ≤ _ := by gcongr

/-- the coordinate swap selected by `σ`. -/
def swapFun (m : ℕ) (σ : Fin m → Bool) : Fin (m + m) → Fin (m + m) :=
  Fin.addCases (motive := fun _ => Fin (m + m))
    (fun i => if σ i then Fin.natAdd m i else Fin.castAdd m i)
    (fun i => if σ i then Fin.castAdd m i else Fin.natAdd m i)

lemma swapFun_invol (m : ℕ) (σ : Fin m → Bool) : Function.Involutive (swapFun m σ) := by
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · unfold swapFun
    by_cases h : σ i <;> simp [h, -Fin.natAdd_eq_addNat]
  · unfold swapFun
    by_cases h : σ i <;> simp [h, -Fin.natAdd_eq_addNat]

lemma swap_formula (m : ℕ) {Y : Type*} (σ : Fin m → Bool) (w : Fin (m + m) → Y) :
    Fin.append (fun i => if σ i then w (Fin.natAdd m i) else w (Fin.castAdd m i))
      (fun i => if σ i then w (Fin.castAdd m i) else w (Fin.natAdd m i)) = w ∘ swapFun m σ := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · unfold swapFun
    by_cases h : σ i <;> simp [h, -Fin.natAdd_eq_addNat]
  · unfold swapFun
    by_cases h : σ i <;> simp [h, -Fin.natAdd_eq_addNat]

lemma measurePreserving_swap {Y : Type*} [MeasurableSpace Y] (Q : Measure Y)
    [IsProbabilityMeasure Q] (m : ℕ) (σ : Fin m → Bool) :
    MeasurePreserving (fun w : Fin (m + m) → Y => w ∘ swapFun m σ)
      (Measure.pi fun _ : Fin (m + m) => Q) (Measure.pi fun _ : Fin (m + m) => Q) := by
  have h2 := measurePreserving_arrowCongr' (fun _ : Fin (m + m) => Q)
    (fun _ : Fin (m + m) => Q) (Function.Involutive.toPerm _ (swapFun_invol m σ))
    (MeasurableEquiv.refl Y) (fun _ => MeasurePreserving.id Q)
  convert h2 using 1
  funext w
  funext j
  simp [MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Equiv.arrowCongr]

open Classical in
/-- C5: swap symmetrization. -/
theorem swap_symmetrization {Y : Type*} [MeasurableSpace Y] (Q : Measure Y)
    [IsProbabilityMeasure Q] (m : ℕ) (J : Set (Fin (m + m) → Y)) (hJ : MeasurableSet J)
    (b : ENNReal)
    (hb : ∀ w : Fin (m + m) → Y, ((Finset.univ.filter fun σ : Fin m → Bool =>
        Fin.append (fun i => if σ i then w (Fin.natAdd m i) else w (Fin.castAdd m i))
          (fun i => if σ i then w (Fin.castAdd m i) else w (Fin.natAdd m i)) ∈ J).card
          : ENNReal) / 2 ^ m ≤ b) :
    Measure.pi (fun _ : Fin (m + m) => Q) J ≤ b := by
  set ν := Measure.pi (fun _ : Fin (m + m) => Q) with hν
  have hpre : ∀ σ : Fin m → Bool,
      ν J = ∫⁻ w, ((fun w : Fin (m + m) → Y => w ∘ swapFun m σ) ⁻¹' J).indicator 1 w ∂ν := by
    intro σ
    have hmp := measurePreserving_swap Q m σ
    rw [lintegral_indicator_one (hmp.measurable hJ), hmp.measure_preimage hJ.nullMeasurableSet]
  have hsum : (2 : ENNReal) ^ m * ν J
      = ∫⁻ w, ∑ σ : Fin m → Bool,
          ((fun w : Fin (m + m) → Y => w ∘ swapFun m σ) ⁻¹' J).indicator 1 w ∂ν := by
    rw [lintegral_finsetSum]
    · rw [← Finset.sum_congr rfl (fun σ _ => hpre σ), Finset.sum_const, Finset.card_univ]
      simp [nsmul_eq_mul]
    · intro σ _
      exact (measurable_one.indicator ((measurePreserving_swap Q m σ).measurable hJ))
  have hpt : ∀ w, ∑ σ : Fin m → Bool,
      ((fun w : Fin (m + m) → Y => w ∘ swapFun m σ) ⁻¹' J).indicator (fun _ => (1 : ENNReal)) w
      ≤ 2 ^ m * b := by
    intro w
    have hbw := hb w
    rw [ENNReal.div_le_iff (by positivity) (by simp)] at hbw
    calc ∑ σ : Fin m → Bool,
          ((fun w : Fin (m + m) → Y => w ∘ swapFun m σ) ⁻¹' J).indicator (fun _ => (1 : ENNReal)) w
        = ((Finset.univ.filter fun σ : Fin m → Bool =>
            Fin.append (fun i => if σ i then w (Fin.natAdd m i) else w (Fin.castAdd m i))
              (fun i => if σ i then w (Fin.castAdd m i) else w (Fin.natAdd m i)) ∈ J).card
              : ENNReal) := by
          rw [Finset.card_filter]
          push_cast
          apply Finset.sum_congr rfl
          intro σ _
          rw [swap_formula]
          simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
      _ ≤ b * 2 ^ m := hbw
      _ = 2 ^ m * b := mul_comm _ _
  have hle : (2 : ENNReal) ^ m * ν J ≤ 2 ^ m * b := by
    rw [hsum]
    calc ∫⁻ w, ∑ σ : Fin m → Bool,
          ((fun w : Fin (m + m) → Y => w ∘ swapFun m σ) ⁻¹' J).indicator 1 w ∂ν
        ≤ ∫⁻ _w, 2 ^ m * b ∂ν := lintegral_mono hpt
      _ = 2 ^ m * b := by rw [lintegral_const, measure_univ, mul_one]
  exact (ENNReal.mul_le_mul_iff_right (by positivity) (by simp)).mp hle

end B4c345


namespace B4glue

open BartlettNN.Margin

lemma sq_ne_iff (γ : ℝ) (hγ : 0 < γ) (α : ℝ) (b : Bool) :
    squash γ α ≠ γ * pm b ↔ pm b * α < γ := by
  unfold squash pm
  cases b
  · simp only [Bool.false_eq_true, if_false]
    constructor
    · intro h
      by_contra h'
      apply h
      rw [min_eq_right (by linarith), max_eq_left (by linarith)]
      ring
    · intro h h'
      have h1 : -γ < min γ α := lt_min (by linarith) (by linarith)
      have h2 : -γ < max (-γ) (min γ α) := lt_max_of_lt_right h1
      linarith
  · simp only [if_true]
    constructor
    · intro h
      by_contra h'
      apply h
      rw [min_eq_left (by linarith), max_eq_right (by linarith)]
      ring
    · intro h h'
      have h1 : min γ α < γ := min_lt_iff.mpr (Or.inr (by linarith))
      have h2 : max (-γ) (min γ α) < γ := max_lt (by linarith) h1
      linarith

lemma sq_far (γ : ℝ) (hγ : 0 < γ) (α : ℝ) (b : Bool) (h : sgn α ≠ pm b) :
    γ ≤ |squash γ α - γ * pm b| := by
  unfold squash pm sgn at *
  cases b
  · simp only [Bool.false_eq_true, if_false] at h ⊢
    have hα : 0 ≤ α := by
      by_contra h'
      push Not at h'
      exact h (if_pos h')
    have h1 : 0 ≤ min γ α := le_min hγ.le hα
    have h2 : 0 ≤ max (-γ) (min γ α) := le_max_of_le_right h1
    rw [abs_of_nonneg (by linarith)]
    linarith
  · simp only [if_true] at h ⊢
    have hα : α < 0 := by
      by_contra h'
      push Not at h'
      exact h (if_neg (not_lt.mpr h'))
    have h1 : min γ α ≤ 0 := min_le_of_right_le hα.le
    have h2 : max (-γ) (min γ α) ≤ 0 := max_le (by linarith) h1
    rw [abs_of_nonpos (by linarith)]
    linarith

lemma dInf_coord {X : Type*} {k : ℕ} (x : Fin k → X) (f g : X → ℝ) (i : Fin k) :
    |f (x i) - g (x i)| ≤ dInf x f g := by
  unfold dInf
  exact le_ciSup (f := fun i => |f (x i) - g (x i)|) (Set.finite_range _).bddAbove i

lemma cover_exists {X : Type*} (F : Set (X → ℝ)) (ε : ℝ) (k : ℕ) (x : Fin k → X) (N : ℕ)
    (hN : Ninf F ε k ≤ N) :
    ∃ T : Finset (X → ℝ), T.card ≤ N ∧ ∀ f ∈ F, ∃ g ∈ T, dInf x g f < ε := by
  by_contra hcon
  push Not at hcon
  have h1 : (((N + 1 : ℕ)) : ℕ∞) ≤ coverNum (dInf x) F ε := by
    unfold coverNum
    apply le_iInf₂
    intro T hT
    have : N + 1 ≤ T.card := by
      by_contra hlt
      obtain ⟨f, hf, hg⟩ := hcon T (by omega)
      obtain ⟨g, hgT, hd⟩ := hT f hf
      exact absurd hd (not_lt.mpr (hg g hgT))
    exact_mod_cast this
  have h2 : coverNum (dInf x) F ε ≤ Ninf F ε k := le_iSup (fun x => coverNum (dInf x) F ε) x
  have h3 := h1.trans (h2.trans hN)
  have : N + 1 ≤ N := by exact_mod_cast h3
  omega

lemma measurable_sgn : Measurable sgn := by
  unfold sgn
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    measurable_const

lemma meas_mis {X : Type*} [MeasurableSpace X] (h : X → ℝ) (hh : Measurable h) :
    MeasurableSet {q : X × Bool | sgn (h q.1) ≠ pm q.2} := by
  have h1 : Measurable fun q : X × Bool => sgn (h q.1) := measurable_sgn.comp (hh.comp measurable_fst)
  have h2 : Measurable fun q : X × Bool => pm q.2 := (measurable_of_countable pm).comp measurable_snd
  exact (measurableSet_eq_fun h1 h2).compl

lemma close_far (γ a b c : ℝ) (hclose : |b - a| < γ / 2) (h : γ ≤ |a - c|) : γ / 2 ≤ |b - c| := by
  have := abs_sub_le a b c
  rw [abs_sub_comm a b] at this
  linarith

lemma close_ne (γ a b c : ℝ) (hclose : |b - a| < γ / 2) (h : γ / 2 ≤ |b - c|) : a ≠ c := by
  intro hac
  rw [hac] at hclose
  linarith

/-- ghost count (last `m` coordinates, misclassified with margin). -/
noncomputable def cG {X : Type*} (γ : ℝ) (h : X → ℝ) {m : ℕ} (w : Fin (m + m) → X × Bool) : ℕ :=
  (Finset.univ.filter fun i : Fin m =>
    γ ≤ |squash γ (h (w (Fin.natAdd m i)).1) - γ * pm (w (Fin.natAdd m i)).2|).card

/-- first-half margin-error count. -/
noncomputable def cF {X : Type*} (γ : ℝ) (h : X → ℝ) {m : ℕ} (w : Fin (m + m) → X × Bool) : ℕ :=
  (Finset.univ.filter fun i : Fin m =>
    squash γ (h (w (Fin.castAdd m i)).1) ≠ γ * pm (w (Fin.castAdd m i)).2).card

set_option maxHeartbeats 1000000 in
open Classical in
theorem main_bound {X : Type*} [MeasurableSpace X]
    (P : Measure (X × Bool)) [IsProbabilityMeasure P] (H : Set (X → ℝ))
    (γ : ℝ) (hγ : 0 < γ) (m : ℕ) (hm : 4 ≤ m)
    (hHmeas : ∀ h ∈ H, Measurable h) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hεm : 2 * Real.log 4 < m * ε ^ 2)
    (hbad : MeasurableSet {z : Fin m → X × Bool | ∃ h ∈ H, erHat γ z h + ε ≤ er P h})
    (hghost : ∀ ε : ℝ, MeasurableSet {w : Fin (m + m) → X × Bool | ∃ h ∈ H,
      ((Finset.univ.filter fun i : Fin m =>
          γ ≤ |squash γ (h (w (Fin.natAdd m i)).1) - γ * pm (w (Fin.natAdd m i)).2|).card : ℝ) / m
        ≥ ((Finset.univ.filter fun i : Fin m =>
          squash γ (h (w (Fin.castAdd m i)).1) ≠ γ * pm (w (Fin.castAdd m i)).2).card : ℝ) / m
          + ε / 2})
    (N : ℕ) (hN : Ninf (squashClass γ H) (γ / 2) (2 * m) ≤ N) :
    Measure.pi (fun _ : Fin m => P) {z | ∃ h ∈ H, erHat γ z h + ε ≤ er P h}
      ≤ 2 * ENNReal.ofReal (N * Real.exp (-((m : ℝ) * ε ^ 2 / 2))) := by
  set s : ℤ := ⌊(m : ℝ) * ε⌋ with hs
  have hmR : (0 : ℝ) < m := by
    have : (4 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  set J : Set (Fin (m + m) → X × Bool) := {w | ∃ h ∈ H,
      (cG γ h w : ℝ) / m ≥ (cF γ h w : ℝ) / m + (2 * (s : ℝ) / m) / 2} with hJdef
  have hJ : MeasurableSet J := hghost (2 * (s : ℝ) / m)
  have memJ : ∀ w, ∀ h ∈ H, (cF γ h w : ℤ) + s ≤ cG γ h w → w ∈ J := by
    intro w h hH hint
    refine ⟨h, hH, ?_⟩
    have hr : (cF γ h w : ℝ) + s ≤ cG γ h w := by exact_mod_cast hint
    rw [ge_iff_le, show (2 * (s : ℝ) / m) / 2 = s / m by ring, ← add_div]
    exact div_le_div_of_nonneg_right hr hmR.le
  have ofJ : ∀ w ∈ J, ∃ h ∈ H, (cF γ h w : ℤ) + s ≤ cG γ h w := by
    rintro w ⟨h, hH, hw⟩
    refine ⟨h, hH, ?_⟩
    rw [ge_iff_le, show (2 * (s : ℝ) / m) / 2 = s / m by ring, ← add_div,
      div_le_div_iff_of_pos_right hmR] at hw
    exact_mod_cast hw
  -- Step G: ghost sample
  have hgh : ∀ z ∈ {z : Fin m → X × Bool | ∃ h ∈ H, erHat γ z h + ε ≤ er P h},
      (1 : ENNReal) / 2 ≤ Measure.pi (fun _ : Fin m => P) {z' | Fin.append z z' ∈ J} := by
    rintro z ⟨h, hH, hle⟩
    set E : Set (X × Bool) := {q | sgn (h q.1) ≠ pm q.2} with hE
    have hEm : MeasurableSet E := meas_mis h (hHmeas h hH)
    have hp0 : 0 ≤ er P h := measureReal_nonneg
    have hp1 : er P h ≤ 1 := measureReal_le_one
    set a := (Finset.univ.filter fun i => pm (z i).2 * h (z i).1 < γ).card with ha
    have haR : erHat γ z h = (a : ℝ) / m := rfl
    have hcF : ∀ z', cF γ h (Fin.append z z') = a := by
      intro z'
      unfold cF
      simp only [Fin.append_left]
      congr 1
      apply Finset.filter_congr
      intro i _
      exact sq_ne_iff γ hγ _ _
    have hcG : ∀ z', (Finset.univ.filter fun i => z' i ∈ E).card ≤ cG γ h (Fin.append z z') := by
      intro z'
      unfold cG
      simp only [Fin.append_right]
      apply Finset.card_le_card
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hi
      exact sq_far γ hγ _ _ hi
    have h1 : (a : ℝ) + m * ε ≤ m * er P h := by
      rw [haR] at hle
      have := mul_le_mul_of_nonneg_left hle hmR.le
      rw [mul_add, mul_div_cancel₀ _ hmR.ne'] at this
      exact this
    have hts : (a : ℤ) + s ≤ ⌊(m : ℝ) * er P h⌋ := by
      rw [hs, ← Int.floor_natCast_add]
      exact Int.floor_mono h1
    have htnat : ((⌊(m : ℝ) * er P h⌋₊ : ℕ) : ℤ) = ⌊(m : ℝ) * er P h⌋ :=
      Int.natCast_floor_eq_floor (by positivity)
    have hsub : {z' : Fin m → X × Bool | ⌊(m : ℝ) * er P h⌋₊ ≤
        (Finset.univ.filter fun i => z' i ∈ E).card} ⊆ {z' | Fin.append z z' ∈ J} := by
      intro z' hz'
      simp only [Set.mem_ofPred_eq] at hz' ⊢
      apply memJ _ h hH
      rw [hcF]
      have := hcG z'
      omega
    have hhalf : (1 : ENNReal) / 2 = ENNReal.ofReal (1 / 2) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
    calc (1 : ENNReal) / 2 = ENNReal.ofReal (1 / 2) := hhalf
      _ ≤ ENNReal.ofReal (∑ k ∈ Finset.Icc ⌊(m : ℝ) * er P h⌋₊ m,
            (m.choose k : ℝ) * (er P h) ^ k * (1 - er P h) ^ (m - k)) :=
          ENNReal.ofReal_le_ofReal (B4c2.binomial_floor_median m _ hp0 hp1)
      _ = Measure.pi (fun _ : Fin m => P) {z' : Fin m → X × Bool | ⌊(m : ℝ) * er P h⌋₊ ≤
            (Finset.univ.filter fun i => z' i ∈ E).card} := by
          convert (B4c345.pi_count_ge_eq P E hEm m ⌊(m : ℝ) * er P h⌋₊).symm <;> rfl
      _ ≤ _ := measure_mono hsub
  have hC4 := B4c345.ghost_symmetrization P m _ hbad J hJ hgh
  -- Step S: swaps + cover + tail
  have hb : ∀ w : Fin (m + m) → X × Bool, ((Finset.univ.filter fun σ : Fin m → Bool =>
      Fin.append (fun i => if σ i then w (Fin.natAdd m i) else w (Fin.castAdd m i))
        (fun i => if σ i then w (Fin.castAdd m i) else w (Fin.natAdd m i)) ∈ J).card
        : ENNReal) / 2 ^ m ≤ ENNReal.ofReal (N * Real.exp (-((m : ℝ) * ε ^ 2 / 2))) := by
    intro w
    let x : Fin (2 * m) → X := fun i => (w (Fin.cast (two_mul m) i)).1
    obtain ⟨T, hTc, hT⟩ := cover_exists (squashClass γ H) (γ / 2) (2 * m) x N hN
    let V : (X → ℝ) → X × Bool → ℤ := fun g q => if γ / 2 ≤ |g q.1 - γ * pm q.2| then 1 else 0
    let c : (X → ℝ) → Fin m → ℤ := fun g i => V g (w (Fin.castAdd m i)) - V g (w (Fin.natAdd m i))
    have hc : ∀ g i, |c g i| ≤ 1 := by
      intro g i
      simp only [c, V]
      split_ifs <;> norm_num
    have hsub : (Finset.univ.filter fun σ : Fin m → Bool =>
        Fin.append (fun i => if σ i then w (Fin.natAdd m i) else w (Fin.castAdd m i))
          (fun i => if σ i then w (Fin.castAdd m i) else w (Fin.natAdd m i)) ∈ J)
        ⊆ T.biUnion (fun g => Finset.univ.filter fun σ : Fin m → Bool =>
            s ≤ ∑ i, (if σ i then c g i else -c g i)) := by
      intro σ hσ
      rw [Finset.mem_filter] at hσ
      set w' := Fin.append (fun i => if σ i then w (Fin.natAdd m i) else w (Fin.castAdd m i))
          (fun i => if σ i then w (Fin.castAdd m i) else w (Fin.natAdd m i)) with hw'
      obtain ⟨h, hH, hint⟩ := ofJ w' hσ.2
      obtain ⟨g, hgT, hd⟩ := hT (squash γ ∘ h) ⟨h, hH, rfl⟩
      rw [Finset.mem_biUnion]
      refine ⟨g, hgT, ?_⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hclose : ∀ j : Fin (m + m), |g (w j).1 - squash γ (h (w j).1)| < γ / 2 := by
        intro j
        have := dInf_coord x g (squash γ ∘ h) (Fin.cast (two_mul m).symm j)
        simp only [x, Function.comp, Fin.cast_cast, Fin.cast_eq_self] at this
        linarith
      have hcN : ∀ i, |g (w' (Fin.natAdd m i)).1 - squash γ (h (w' (Fin.natAdd m i)).1)| < γ / 2 := by
        intro i
        simp only [w', Fin.append_right]
        split_ifs <;> exact hclose _
      have hcC : ∀ i, |g (w' (Fin.castAdd m i)).1 - squash γ (h (w' (Fin.castAdd m i)).1)| < γ / 2 := by
        intro i
        simp only [w', Fin.append_left]
        split_ifs <;> exact hclose _
      have hG : (cG γ h w' : ℤ) ≤ ∑ i, V g (w' (Fin.natAdd m i)) := by
        unfold cG
        rw [Finset.card_filter]
        push_cast
        apply Finset.sum_le_sum
        intro i _
        split_ifs with h1
        · have := close_far γ _ _ _ (hcN i) h1
          simp only [V, if_pos this, le_refl]
        · simp only [V]; split_ifs <;> norm_num
      have hF : ∑ i, V g (w' (Fin.castAdd m i)) ≤ (cF γ h w' : ℤ) := by
        unfold cF
        rw [Finset.card_filter]
        push_cast
        apply Finset.sum_le_sum
        intro i _
        simp only [V]
        split_ifs with h1 h2 <;> first | exact absurd (close_ne γ _ _ _ (hcC i) h1) h2 | norm_num
      have hsum : ∑ i, (if σ i then c g i else -c g i)
          = ∑ i, (V g (w' (Fin.natAdd m i)) - V g (w' (Fin.castAdd m i))) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [w', Fin.append_left, Fin.append_right, c]
        cases σ i <;> simp
      rw [hsum, Finset.sum_sub_distrib]
      linarith
    have hE := Real.exp_pos (-((m : ℝ) * ε ^ 2 / 2))
    have hcardR : ((Finset.univ.filter fun σ : Fin m → Bool =>
        Fin.append (fun i => if σ i then w (Fin.natAdd m i) else w (Fin.castAdd m i))
          (fun i => if σ i then w (Fin.castAdd m i) else w (Fin.natAdd m i)) ∈ J).card : ℝ)
        ≤ N * Real.exp (-((m : ℝ) * ε ^ 2 / 2)) * 2 ^ m := by
      have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      have h1R : ((Finset.univ.filter fun σ : Fin m → Bool =>
          Fin.append (fun i => if σ i then w (Fin.natAdd m i) else w (Fin.castAdd m i))
            (fun i => if σ i then w (Fin.castAdd m i) else w (Fin.natAdd m i)) ∈ J).card : ℝ)
          ≤ ∑ g ∈ T, ((Finset.univ.filter fun σ : Fin m → Bool =>
            s ≤ ∑ i, (if σ i then c g i else -c g i)).card : ℝ) := by exact_mod_cast h1
      have h2 : ∀ g ∈ T, ((Finset.univ.filter fun σ : Fin m → Bool =>
            s ≤ ∑ i, (if σ i then c g i else -c g i)).card : ℝ)
            ≤ Real.exp (-((m : ℝ) * ε ^ 2 / 2)) * 2 ^ m := by
        intro g _
        have := B4c1.rademacher_tail_floor m hm (c g) (hc g) ε hε0 hε1 hεm
        rw [div_le_iff₀ (by positivity)] at this
        exact this
      have h3 := Finset.sum_le_sum h2
      rw [Finset.sum_const, nsmul_eq_mul] at h3
      have hTR : (T.card : ℝ) ≤ N := by exact_mod_cast hTc
      have : (T.card : ℝ) * (Real.exp (-((m : ℝ) * ε ^ 2 / 2)) * 2 ^ m)
          ≤ N * (Real.exp (-((m : ℝ) * ε ^ 2 / 2)) * 2 ^ m) :=
        mul_le_mul_of_nonneg_right hTR (by positivity)
      linarith
    rw [ENNReal.div_le_iff (by positivity) (by simp)]
    calc ((Finset.univ.filter fun σ : Fin m → Bool =>
        Fin.append (fun i => if σ i then w (Fin.natAdd m i) else w (Fin.castAdd m i))
          (fun i => if σ i then w (Fin.castAdd m i) else w (Fin.natAdd m i)) ∈ J).card : ENNReal)
        = ENNReal.ofReal ((Finset.univ.filter fun σ : Fin m → Bool =>
        Fin.append (fun i => if σ i then w (Fin.natAdd m i) else w (Fin.castAdd m i))
          (fun i => if σ i then w (Fin.castAdd m i) else w (Fin.natAdd m i)) ∈ J).card : ℝ) :=
          (ENNReal.ofReal_natCast _).symm
      _ ≤ ENNReal.ofReal (N * Real.exp (-((m : ℝ) * ε ^ 2 / 2)) * 2 ^ m) :=
          ENNReal.ofReal_le_ofReal hcardR
      _ = ENNReal.ofReal (N * Real.exp (-((m : ℝ) * ε ^ 2 / 2))) * 2 ^ m := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
          simp
  have hC5 := B4c345.swap_symmetrization P m J hJ _ hb
  calc _ ≤ 2 * Measure.pi (fun _ : Fin (m + m) => P) J := hC4
    _ ≤ _ := by gcongr


lemma m3_bound {X : Type*} [MeasurableSpace X] (P : Measure (X × Bool)) [IsProbabilityMeasure P]
    (H : Set (X → ℝ)) (γ : ℝ) (hγ : 0 < γ) (hHmeas : ∀ h ∈ H, Measurable h) (ε : ℝ)
    (hε : 2 / 3 < ε)
    (hsingle : ∀ h ∈ H, ∀ h' ∈ H, ∀ x : X, |squash γ (h x) - squash γ (h' x)| < γ) :
    Measure.pi (fun _ : Fin 3 => P) {z | ∃ h ∈ H, erHat γ z h + ε ≤ er P h}
      ≤ ENNReal.ofReal ((1 / 3) ^ 3) := by
  by_cases hA : {z : Fin 3 → X × Bool | ∃ h ∈ H, erHat γ z h + ε ≤ er P h} = ∅
  · rw [hA, measure_empty]; exact bot_le
  obtain ⟨z0, h0, hH0, hle0⟩ := Set.nonempty_iff_ne_empty.mpr hA
  have hEr0 : 0 ≤ erHat γ z0 h0 := by unfold erHat; positivity
  have her0 : ε ≤ er P h0 := by linarith
  set Cor : Set (X × Bool) := {q | sgn (h0 q.1) ≠ pm q.2}ᶜ with hCor_def
  have hsubset : {z : Fin 3 → X × Bool | ∃ h ∈ H, erHat γ z h + ε ≤ er P h}
      ⊆ Set.pi Set.univ (fun _ => Cor) := by
    rintro z ⟨h, hH, hle⟩ i _
    have her1 : er P h ≤ 1 := measureReal_le_one
    have hlt : erHat γ z h < 1 / 3 := by linarith
    have hcard : (Finset.univ.filter fun i => pm (z i).2 * h (z i).1 < γ).card = 0 := by
      unfold erHat at hlt
      push_cast at hlt
      have : ((Finset.univ.filter fun i => pm (z i).2 * h (z i).1 < γ).card : ℝ) < 1 := by
        linarith
      have : (Finset.univ.filter fun i => pm (z i).2 * h (z i).1 < γ).card < 1 := by
        exact_mod_cast this
      omega
    have hi : ¬ (pm (z i).2 * h (z i).1 < γ) := by
      intro hi
      rw [Finset.card_eq_zero] at hcard
      have : i ∈ (Finset.univ.filter fun i => pm (z i).2 * h (z i).1 < γ) := by simp [hi]
      rw [hcard] at this
      exact absurd this (Finset.notMem_empty i)
    have hsq : squash γ (h (z i).1) = γ * pm (z i).2 := by
      by_contra hne
      exact hi ((sq_ne_iff γ hγ _ _).mp hne)
    have hcl := hsingle h0 hH0 h hH (z i).1
    rw [hsq] at hcl
    simp only [hCor_def, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not]
    by_contra hne
    have := sq_far γ hγ _ _ hne
    linarith
  have hCor : P Cor ≤ ENNReal.ofReal (1 / 3) := by
    have hm := meas_mis h0 (hHmeas h0 hH0)
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    apply ENNReal.ofReal_le_ofReal
    rw [hCor_def, probReal_compl_eq_one_sub hm]
    have : er P h0 = P.real {q | sgn (h0 q.1) ≠ pm q.2} := rfl
    linarith
  calc _ ≤ Measure.pi (fun _ : Fin 3 => P) (Set.pi Set.univ (fun _ => Cor)) := measure_mono hsubset
    _ = ∏ _i : Fin 3, P Cor := Measure.pi_pi _ _
    _ ≤ ∏ _i : Fin 3, ENNReal.ofReal (1 / 3) := Finset.prod_le_prod' (fun _ _ => hCor)
    _ = ENNReal.ofReal ((1 / 3) ^ 3) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.ofReal_pow (by norm_num)]

end B4glue

set_option maxHeartbeats 1000000 in
open BartlettNN.Margin MeasureTheory in
theorem solution {X : Type*} [MeasurableSpace X]
    (P : Measure (X × Bool)) [IsProbabilityMeasure P] (H : Set (X → ℝ))
    (γ δ : ℝ) (hγ : 0 < γ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) (m : ℕ) (hm : 1 ≤ m)
    (hHmeas : ∀ h ∈ H, Measurable h)
    (hbad : ∀ ε : ℝ, MeasurableSet {z : Fin m → X × Bool | ∃ h ∈ H, erHat γ z h + ε ≤ er P h})
    (hghost : ∀ ε : ℝ, MeasurableSet {w : Fin (m + m) → X × Bool | ∃ h ∈ H,
      ((Finset.univ.filter fun i : Fin m =>
          γ ≤ |squash γ (h (w (Fin.natAdd m i)).1) - γ * pm (w (Fin.natAdd m i)).2|).card : ℝ) / m
        ≥ ((Finset.univ.filter fun i : Fin m =>
          squash γ (h (w (Fin.castAdd m i)).1) ≠ γ * pm (w (Fin.castAdd m i)).2).card : ℝ) / m
          + ε / 2})
    (N : ℕ) (hN : Ninf (squashClass γ H) (γ / 2) (2 * m) ≤ N) :
    Measure.pi (fun _ : Fin m => P)
      {z | ∃ h ∈ H, erHat γ z h + Real.sqrt ((2 / m) * Real.log (2 * N / δ)) ≤ er P h}
      ≤ ENNReal.ofReal δ := by
  set L := Real.log (2 * N / δ) with hL
  set ε := Real.sqrt ((2 / m) * L) with hε
  by_cases hA : {z : Fin m → X × Bool | ∃ h ∈ H, erHat γ z h + ε ≤ er P h} = ∅
  · rw [hA, measure_empty]; exact bot_le
  obtain ⟨z0, h0, hH0, hle0⟩ := Set.nonempty_iff_ne_empty.mpr hA
  have hEr0 : 0 ≤ erHat γ z0 h0 := by unfold erHat; positivity
  have her1 : er P h0 ≤ 1 := measureReal_le_one
  have hεle : ε ≤ 1 := by linarith
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hN1 : 1 ≤ N := by
    by_contra hN0
    have hN0' : N = 0 := by omega
    obtain ⟨T, hTc, hT⟩ := B4glue.cover_exists (squashClass γ H) (γ / 2) (2 * m)
      (fun _ => (z0 ⟨0, by omega⟩).1) N hN
    rw [hN0'] at hTc
    have hT0 : T = ∅ := Finset.card_eq_zero.mp (by omega)
    obtain ⟨g, hg, _⟩ := hT (squash γ ∘ h0) ⟨h0, hH0, rfl⟩
    rw [hT0] at hg
    exact absurd hg (Finset.notMem_empty g)
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have h2N : 4 < 2 * (N : ℝ) / δ := by
    rw [lt_div_iff₀ hδ0]; nlinarith
  have hlog4 : Real.log 4 < L := Real.log_lt_log (by norm_num) h2N
  have hlog2 := Real.log_two_gt_d9
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hLpos : 0 < L := by linarith
  have hε2 : ε ^ 2 = (2 / m) * L := Real.sq_sqrt (by positivity)
  have hmε : (m : ℝ) * ε ^ 2 = 2 * L := by rw [hε2]; field_simp
  have hε0 : 0 < ε := Real.sqrt_pos.mpr (by positivity)
  have hexpL : Real.exp L = 2 * N / δ := Real.exp_log (by positivity)
  have hδeq : δ = 2 * (N * Real.exp (-((m : ℝ) * ε ^ 2 / 2))) := by
    rw [hmε, show 2 * L / 2 = L by ring, Real.exp_neg, hexpL]
    field_simp
  rcases (show m ≤ 2 ∨ m = 3 ∨ 4 ≤ m by omega) with hm2 | hm3 | hm4
  · exfalso
    have hm2R : (m : ℝ) ≤ 2 := by exact_mod_cast hm2
    have h1 : (1 : ℝ) ≤ 2 / m := by rw [le_div_iff₀ (by linarith)]; linarith
    have : 1 < ε ^ 2 := by rw [hε2]; nlinarith
    nlinarith
  · subst hm3
    have hm3R : ((3 : ℕ) : ℝ) = 3 := by norm_num
    rw [hm3R] at hmε hδeq
    have hL15 : L ≤ 3 / 2 := by nlinarith
    have hN1' : N = 1 := by
      by_contra hne
      have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
      have h8 : 8 < 2 * (N : ℝ) / δ := by rw [lt_div_iff₀ hδ0]; nlinarith
      have hlog8 : Real.log 8 < L := Real.log_lt_log (by norm_num) h8
      have hlog8eq : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
      linarith
    have hsingle : ∀ h ∈ H, ∀ h' ∈ H, ∀ x : X, |squash γ (h x) - squash γ (h' x)| < γ := by
      intro h hH h' hH' x
      obtain ⟨T, hTc, hT⟩ := B4glue.cover_exists (squashClass γ H) (γ / 2) (2 * 3)
        (fun _ => x) N hN
      rw [hN1'] at hTc
      obtain ⟨g, hg, hd⟩ := hT (squash γ ∘ h) ⟨h, hH, rfl⟩
      obtain ⟨g', hg', hd'⟩ := hT (squash γ ∘ h') ⟨h', hH', rfl⟩
      have hgg : g = g' := Finset.card_le_one.mp hTc g hg g' hg'
      rw [← hgg] at hd'
      have e1 := B4glue.dInf_coord (fun _ : Fin (2 * 3) => x) g (squash γ ∘ h) ⟨0, by norm_num⟩
      have e2 := B4glue.dInf_coord (fun _ : Fin (2 * 3) => x) g (squash γ ∘ h') ⟨0, by norm_num⟩
      simp only [Function.comp] at e1 e2
      have := abs_sub_le (squash γ (h x)) (g x) (squash γ (h' x))
      rw [abs_sub_comm (squash γ (h x)) (g x)] at this
      linarith
    have hε23 : 2 / 3 < ε := by nlinarith
    refine (B4glue.m3_bound P H γ hγ hHmeas ε hε23 hsingle).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hδeq, hN1']
    have he : Real.exp (-(3 / 2 : ℝ)) ≤ Real.exp (-(3 * ε ^ 2 / 2)) := by
      apply Real.exp_le_exp.mpr; nlinarith
    have he2 : Real.exp (3 / 2 : ℝ) ≤ 54 := by
      have h1 := Real.exp_one_lt_d9
      have h2 : Real.exp (3 / 2 : ℝ) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
      have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos 1]
    have he3 : (1 : ℝ) / 54 ≤ Real.exp (-(3 / 2 : ℝ)) := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (Real.exp_pos _) he2
    push_cast
    nlinarith
  · rw [hδeq, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    exact B4glue.main_bound P H γ hγ m hm4 hHmeas ε hε0 hεle (by rw [hmε]; linarith) (hbad ε)
      hghost N hN

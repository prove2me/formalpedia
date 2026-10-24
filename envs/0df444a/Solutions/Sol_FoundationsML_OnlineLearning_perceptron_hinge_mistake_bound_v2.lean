-- Prove2me | solution 1 for FoundationsML.OnlineLearning.perceptron_hinge_mistake_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T08:14:17.196857+00:00
-- url     : https://prove2.me/submissions/4f2e8749-a3b8-4364-8cec-1bd6b8f72035

import Mathlib
import Definitions.Def_FoundationsML_OnlineLearning_PerceptronNumUpdates

open FoundationsML.OnlineLearning

namespace PC88

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma updates_succ (x : ℕ → V) (y : ℕ → ℝ) (n : ℕ) :
    PerceptronUpdates x y (n + 1) =
      if y n * (inner (𝕜 := ℝ) (PerceptronWeight x y n) (x n) : ℝ) ≤ 0
      then insert n (PerceptronUpdates x y n) else PerceptronUpdates x y n := by
  unfold PerceptronUpdates
  rw [Finset.range_add_one, Finset.filter_insert]

lemma not_mem_updates (x : ℕ → V) (y : ℕ → ℝ) (n : ℕ) : n ∉ PerceptronUpdates x y n := by
  simp [PerceptronUpdates]

lemma weight_eq (x : ℕ → V) (y : ℕ → ℝ) (n : ℕ) :
    PerceptronWeight x y n = ∑ t ∈ PerceptronUpdates x y n, y t • x t := by
  induction n with
  | zero => simp [PerceptronWeight, PerceptronUpdates]
  | succ n ih =>
    rw [updates_succ]
    by_cases hc : y n * (inner (𝕜 := ℝ) (PerceptronWeight x y n) (x n) : ℝ) ≤ 0
    · rw [if_pos hc, Finset.sum_insert (not_mem_updates x y n), ← ih]
      simp only [PerceptronWeight, if_pos hc]; abel
    · rw [if_neg hc, ← ih]; simp only [PerceptronWeight, if_neg hc]

lemma weight_norm (x : ℕ → V) (y : ℕ → ℝ) (hy : ∀ t, y t = 1 ∨ y t = -1) (n : ℕ) :
    ‖PerceptronWeight x y n‖ ^ 2 ≤ ∑ t ∈ PerceptronUpdates x y n, ‖x t‖ ^ 2 := by
  induction n with
  | zero => simp [PerceptronWeight, PerceptronUpdates]
  | succ n ih =>
    rw [updates_succ]
    by_cases hc : y n * (inner (𝕜 := ℝ) (PerceptronWeight x y n) (x n) : ℝ) ≤ 0
    · rw [if_pos hc, Finset.sum_insert (not_mem_updates x y n)]
      simp only [PerceptronWeight, if_pos hc]
      have hy2 : y n ^ 2 = 1 := by rcases hy n with h | h <;> simp [h]
      have e : ‖PerceptronWeight x y n + y n • x n‖ ^ 2 =
          ‖PerceptronWeight x y n‖ ^ 2 + 2 * (y n * inner (𝕜 := ℝ) (PerceptronWeight x y n) (x n))
            + y n ^ 2 * ‖x n‖ ^ 2 := by
        rw [@norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      rw [e, hy2]; nlinarith
    · rw [if_neg hc]; simp only [PerceptronWeight, if_neg hc]; exact ih

lemma quad_root {s a L : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a) (hL : 0 ≤ L) (h : s ^ 2 - L ≤ a * s) :
    s ^ 2 ≤ ((a + Real.sqrt (a ^ 2 + 4 * L)) / 2) ^ 2 := by
  set R := Real.sqrt (a ^ 2 + 4 * L)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = a ^ 2 + 4 * L := Real.sq_sqrt (by positivity)
  have hsr : s ≤ (a + R) / 2 := by
    by_contra hc; push Not at hc
    have h1 : 0 < s - (a + R) / 2 := by linarith
    have h2 : 0 < s - (a - R) / 2 := by linarith
    have := mul_pos h1 h2
    nlinarith
  exact pow_le_pow_left₀ hs hsr 2

end PC88

open FoundationsML.OnlineLearning in
theorem solution
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x : ℕ → V) (y : ℕ → ℝ) (hy : ∀ t, y t = 1 ∨ y t = -1)
    (T : ℕ) (r : ℝ) (hr : 0 < r) (hxr : ∀ t < T, ‖x t‖ ≤ r) :
    (PerceptronNumUpdates x y T : ℝ) ≤
      sInf ((fun q : ℝ × V =>
        ((r / q.1 + Real.sqrt (r ^ 2 / q.1 ^ 2 +
            4 * ∑ t ∈ PerceptronUpdates x y T,
              max 0 (1 - y t * (inner (𝕜 := ℝ) q.2 (x t) : ℝ) / q.1))) /
          2) ^ 2) '' {q : ℝ × V | 0 < q.1 ∧ ‖q.2‖ ≤ 1}) := by
  set U := PerceptronUpdates x y T with hU
  set M : ℝ := (PerceptronNumUpdates x y T : ℝ) with hM
  have hMU : M = (U.card : ℝ) := rfl
  have hUT : ∀ t ∈ U, t < T := fun t ht => by
    exact Finset.mem_range.1 (Finset.mem_filter.1 ht).1
  apply le_csInf
  · exact ⟨_, ⟨(1, 0), ⟨one_pos, by simp⟩, rfl⟩⟩
  rintro b ⟨⟨ρ, u⟩, ⟨hρ, hu⟩, rfl⟩
  simp only
  set L := ∑ t ∈ U, max 0 (1 - y t * (inner (𝕜 := ℝ) u (x t) : ℝ) / ρ) with hL
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun t _ => le_max_left _ _
  -- M - L ≤ ⟨u, w⟩ / ρ
  have h1 : M - L ≤ (∑ t ∈ U, y t * (inner (𝕜 := ℝ) u (x t) : ℝ)) / ρ := by
    rw [hMU, Finset.sum_div, hL, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro t _
    have := le_max_right 0 (1 - y t * (inner (𝕜 := ℝ) u (x t) : ℝ) / ρ)
    linarith
  have hw := PC88.weight_eq x y T
  have hinner : ∑ t ∈ U, y t * (inner (𝕜 := ℝ) u (x t) : ℝ) =
      inner (𝕜 := ℝ) u (PerceptronWeight x y T) := by
    rw [hw, inner_sum]; simp [inner_smul_right, hU]
  have hwn := PC88.weight_norm x y hy T
  have hsum : ∑ t ∈ U, ‖x t‖ ^ 2 ≤ M * r ^ 2 := by
    calc ∑ t ∈ U, ‖x t‖ ^ 2 ≤ ∑ _t ∈ U, r ^ 2 :=
          Finset.sum_le_sum fun t ht => pow_le_pow_left₀ (norm_nonneg _) (hxr t (hUT t ht)) 2
      _ = M * r ^ 2 := by rw [hMU, Finset.sum_const, nsmul_eq_mul]
  have hM0 : 0 ≤ M := by rw [hMU]; positivity
  have hwle : ‖PerceptronWeight x y T‖ ≤ r * Real.sqrt M := by
    have h2 : ‖PerceptronWeight x y T‖ ^ 2 ≤ (r * Real.sqrt M) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hM0]; linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  have hcs : inner (𝕜 := ℝ) u (PerceptronWeight x y T) ≤ r * Real.sqrt M := by
    calc inner (𝕜 := ℝ) u (PerceptronWeight x y T) ≤ ‖u‖ * ‖PerceptronWeight x y T‖ :=
          real_inner_le_norm _ _
      _ ≤ 1 * ‖PerceptronWeight x y T‖ := by gcongr
      _ ≤ _ := by rw [one_mul]; exact hwle
  have key : (Real.sqrt M) ^ 2 - L ≤ (r / ρ) * Real.sqrt M := by
    rw [Real.sq_sqrt hM0]
    have := div_le_div_of_nonneg_right hcs hρ.le
    rw [hinner] at h1
    calc M - L ≤ inner (𝕜 := ℝ) u (PerceptronWeight x y T) / ρ := h1
      _ ≤ r * Real.sqrt M / ρ := this
      _ = r / ρ * Real.sqrt M := by ring
  have := PC88.quad_root (Real.sqrt_nonneg M) (by positivity) hL0 key
  rw [Real.sq_sqrt hM0, div_pow r ρ 2] at this
  exact this

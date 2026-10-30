-- Prove2me | solution 1 for DecBilevel.SLDBO.lemma_A_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T01:02:03.668997+00:00
-- url     : https://prove2.me/submissions/41c26edd-8618-46a7-bb4d-4b81d0885cc2

import Mathlib
import Definitions.Def_DecBilevel_SLDBO_Setting

namespace DecBilevel.SLDBO.Aux
open DecBilevel.SLDBO Finset

lemma W_symm {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ} {ρ : ℝ} (h : Assumption22 W ρ)
    (i j : Fin n) : W i j = W j i := by
  have := congrFun (congrFun h.symm j) i
  simpa [Matrix.transpose_apply] using this

lemma col_sum {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ} {ρ : ℝ} (h : Assumption22 W ρ)
    (j : Fin n) : ∑ i, W i j = 1 := by
  rw [← h.row_sum j]; exact Finset.sum_congr rfl (fun i _ => W_symm h i j)

lemma norm_sq_eq_sum {d : ℕ} (v : E d) : ‖v‖ ^ 2 = ∑ c, (v c) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp

lemma sum_smul_apply {n d : ℕ} (w : Fin n → ℝ) (z : Fin n → E d) (c : Fin d) :
    (∑ j, w j • z j) c = ∑ j, w j * z j c := by simp

lemma avg_add {n d : ℕ} (a b : Fin n → E d) : avg (fun i => a i + b i) = avg a + avg b := by
  simp [avg, Finset.sum_add_distrib, smul_add]

lemma avg_sub {n d : ℕ} (a b : Fin n → E d) : avg (fun i => a i - b i) = avg a - avg b := by
  simp [avg, Finset.sum_sub_distrib, smul_sub]

lemma avg_smul {n d : ℕ} (t : ℝ) (a : Fin n → E d) : avg (fun i => t • a i) = t • avg a := by
  simp [avg, ← Finset.smul_sum, smul_comm t]

lemma avg_zero {n d : ℕ} : avg (0 : Fin n → E d) = 0 := by simp [avg]

lemma avg_const {n d : ℕ} (hn : 0 < n) (c : E d) : avg (fun _ : Fin n => c) = c := by
  simp only [avg, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, one_div_mul_cancel (by exact_mod_cast hn.ne'),
    one_smul]

lemma avg_mix {n d : ℕ} {W : Matrix (Fin n) (Fin n) ℝ} {ρ : ℝ} (h : Assumption22 W ρ)
    (z : Fin n → E d) : avg (fun i => ∑ j, W i j • z j) = avg z := by
  unfold avg; congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_smul, col_sum h j, one_smul]

lemma sum_sub_avg {n d : ℕ} (z : Fin n → E d) : ∑ i, (z i - avg z) = 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, avg,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_one_div_cancel (by exact_mod_cast hn.ne'),
    one_smul, sub_self]

lemma mix_sub_avg {n d : ℕ} {W : Matrix (Fin n) (Fin n) ℝ} {ρ : ℝ} (h : Assumption22 W ρ)
    (z : Fin n → E d) (c : E d) (i : Fin n) :
    (∑ j, W i j • z j) - c = ∑ j, W i j • (z j - c) := by
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, h.row_sum i, one_smul]

/-- `∑‖zᵢ − c‖² = ∑‖zᵢ − z̄‖² + n‖z̄ − c‖²`, so the mean minimizes. -/
lemma sum_sq_sub_avg_le {n d : ℕ} (z : Fin n → E d) (c : E d) :
    ∑ i, ‖z i - avg z‖ ^ 2 ≤ ∑ i, ‖z i - c‖ ^ 2 := by
  have key : ∀ i, ‖z i - c‖ ^ 2 =
      ‖z i - avg z‖ ^ 2 + 2 * inner ℝ (z i - avg z) (avg z - c) + ‖avg z - c‖ ^ 2 := by
    intro i
    have : z i - c = (z i - avg z) + (avg z - c) := by abel
    rw [this, norm_add_sq_real]
  simp_rw [key, Finset.sum_add_distrib, ← Finset.mul_sum, ← sum_inner, sum_sub_avg]
  simp only [inner_zero_left, mul_zero, add_zero]
  have : 0 ≤ ∑ i : Fin n, ‖avg z - c‖ ^ 2 := by positivity
  linarith

lemma sum_sq_sub_avg_le_sum_sq {n d : ℕ} (z : Fin n → E d) :
    ∑ i, ‖z i - avg z‖ ^ 2 ≤ ∑ i, ‖z i‖ ^ 2 := by
  simpa using sum_sq_sub_avg_le z 0

/-- Jensen for a probability vector: `‖∑ wⱼ zⱼ‖² ≤ ∑ wⱼ ‖zⱼ‖²`. -/
lemma norm_sq_wsum_le {n d : ℕ} (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (h1 : ∑ j, w j = 1)
    (z : Fin n → E d) : ‖∑ j, w j • z j‖ ^ 2 ≤ ∑ j, w j * ‖z j‖ ^ 2 := by
  set m := ∑ j, w j • z j
  have h0 : 0 ≤ ∑ j, w j * ‖z j - m‖ ^ 2 :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hw j) (sq_nonneg _))
  have e : ∑ j, w j * ‖z j - m‖ ^ 2 = ∑ j, w j * ‖z j‖ ^ 2 - ‖m‖ ^ 2 := by
    simp_rw [norm_sub_sq_real, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have h2 : ∑ j, w j * (2 * inner ℝ (z j) m) = 2 * ‖m‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      have : ∑ j, w j * (2 * inner ℝ (z j) m) = 2 * ∑ j, inner ℝ (w j • z j) m := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [real_inner_smul_left]; ring
      rw [this, ← sum_inner]
    rw [h2, ← Finset.sum_mul, h1]; ring
  linarith

theorem lemmaA1 {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) (hA22 : Assumption22 W ρ)
    {d : ℕ} (z : Fin n → E d) :
    (∑ i, ‖∑ j, W i j • z j‖ ^ 2 ≤ ∑ j, ‖z j‖ ^ 2) ∧
    (∑ i, ‖∑ j, W i j • (z j - avg z)‖ ^ 2 ≤ ρ ^ 2 * ∑ i, ‖z i - avg z‖ ^ 2) := by
  constructor
  · calc ∑ i, ‖∑ j, W i j • z j‖ ^ 2 ≤ ∑ i, ∑ j, W i j * ‖z j‖ ^ 2 :=
          Finset.sum_le_sum (fun i _ => norm_sq_wsum_le _ (hA22.nonneg i) (hA22.row_sum i) z)
      _ = ∑ j, ‖z j‖ ^ 2 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [← Finset.sum_mul, col_sum hA22 j, one_mul]
  · set u := fun j => z j - avg z with hu
    have hsum : ∀ c : Fin d, ∑ j, u j c = 0 := by
      intro c
      have := congrArg (fun v : E d => v c) (sum_sub_avg z)
      simpa [hu] using this
    have hc : ∀ c : Fin d, ∑ i, (∑ j, W i j * u j c) ^ 2 ≤ ρ ^ 2 * ∑ i, (u i c) ^ 2 := by
      intro c
      have h := hA22.contract (fun j => u j c) (hsum c)
      have h' := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
      rwa [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at h'
    calc ∑ i, ‖∑ j, W i j • u j‖ ^ 2 = ∑ c, ∑ i, (∑ j, W i j * u j c) ^ 2 := by
          simp_rw [norm_sq_eq_sum, sum_smul_apply]; rw [Finset.sum_comm]
      _ ≤ ∑ c, ρ ^ 2 * ∑ i, (u i c) ^ 2 := Finset.sum_le_sum (fun c _ => hc c)
      _ = ρ ^ 2 * ∑ i, ‖u i‖ ^ 2 := by
          rw [← Finset.mul_sum]; congr 1
          simp_rw [norm_sq_eq_sum]; rw [Finset.sum_comm]

/-! ### Euclidean projection onto the ball -/

lemma ballProj_norm_le {d : ℕ} {r : ℝ} (hr : 0 ≤ r) (z : E d) : ‖ballProj r z‖ ≤ r := by
  unfold ballProj
  split_ifs with h
  · exact h
  · push Not at h
    have hz : 0 < ‖z‖ := lt_of_le_of_lt hr h
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr hz.le), div_mul_cancel₀ _ hz.ne']

lemma ballProj_of_le {d : ℕ} {r : ℝ} {z : E d} (h : ‖z‖ ≤ r) : ballProj r z = z := by
  simp [ballProj, h]

/-- Variational inequality: `⟪z − P z, w − P z⟫ ≤ 0` for `‖w‖ ≤ r`. -/
lemma ballProj_vi {d : ℕ} {r : ℝ} (hr : 0 ≤ r) (z w : E d) (hw : ‖w‖ ≤ r) :
    inner ℝ (z - ballProj r z) (w - ballProj r z) ≤ 0 := by
  unfold ballProj
  split_ifs with h
  · simp
  · push Not at h
    have hz : 0 < ‖z‖ := lt_of_le_of_lt hr h
    have e : z - (r / ‖z‖) • z = (1 - r / ‖z‖) • z := by rw [sub_smul, one_smul]
    rw [e, real_inner_smul_left, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    have hc : 0 ≤ 1 - r / ‖z‖ := by
      rw [sub_nonneg, div_le_one hz]; exact h.le
    apply mul_nonpos_of_nonneg_of_nonpos hc
    have h1 : inner ℝ z w ≤ ‖z‖ * ‖w‖ := real_inner_le_norm z w
    have h2 : r / ‖z‖ * ‖z‖ ^ 2 = r * ‖z‖ := by field_simp
    rw [h2]; nlinarith

lemma ballProj_nonexp {d : ℕ} {r : ℝ} (hr : 0 ≤ r) (x y : E d) :
    ‖ballProj r x - ballProj r y‖ ≤ ‖x - y‖ := by
  set a := ballProj r x
  set b := ballProj r y
  have h1 := ballProj_vi hr x b (ballProj_norm_le hr y)
  have h2 := ballProj_vi hr y a (ballProj_norm_le hr x)
  have key : ‖a - b‖ ^ 2 ≤ inner ℝ (x - y) (a - b) := by
    rw [← real_inner_self_eq_norm_sq]
    have e1 : inner ℝ (x - a) (b - a) + inner ℝ (y - b) (a - b) =
        inner ℝ (a - b) (a - b) - inner ℝ (x - y) (a - b) := by
      have : b - a = -(a - b) := by abel
      rw [this, inner_neg_right]
      simp only [inner_sub_left]; ring
    linarith
  have h3 : inner ℝ (x - y) (a - b) ≤ ‖x - y‖ * ‖a - b‖ := real_inner_le_norm _ _
  have h4 : ‖a - b‖ ^ 2 ≤ ‖x - y‖ * ‖a - b‖ := le_trans key h3
  rcases (norm_nonneg (a - b)).eq_or_lt with h0 | h0
  · rw [← h0]; exact norm_nonneg _
  · nlinarith

theorem lemmaA2 {n d : ℕ} (r : ℝ) (hr : 0 ≤ r) (z : Fin n → E d) :
    ∑ i, ‖ballProj r (z i) - avg (fun j => ballProj r (z j))‖ ^ 2 ≤
      ∑ i, ‖z i - avg z‖ ^ 2 := by
  calc _ ≤ ∑ i, ‖ballProj r (z i) - ballProj r (avg z)‖ ^ 2 :=
        sum_sq_sub_avg_le (fun j => ballProj r (z j)) _
    _ ≤ _ := Finset.sum_le_sum (fun i _ =>
        pow_le_pow_left₀ (norm_nonneg _) (ballProj_nonexp hr _ _) 2)

end DecBilevel.SLDBO.Aux

open DecBilevel.SLDBO

theorem solution {n d : ℕ} (r : ℝ) (hr : 0 ≤ r) (z : Fin n → E d) :
    ∑ i, ‖ballProj r (z i) - avg (fun j => ballProj r (z j))‖ ^ 2 ≤
      ∑ i, ‖z i - avg z‖ ^ 2 :=
  DecBilevel.SLDBO.Aux.lemmaA2 r hr z

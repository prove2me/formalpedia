-- Prove2me | solution 1 for DecBilevel.SLDBO.lemma_A_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T02:29:53.263077+00:00
-- url     : https://prove2.me/submissions/98fb37b4-eb45-4432-bbec-5aa4436f09b5

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

namespace DecBilevel.SLDBO.Aux
open DecBilevel.SLDBO Finset

/-! ### Scalar / sum inequalities -/

lemma young_rho {ρ x y : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    ρ ^ 2 * (x + y) ^ 2 ≤ ρ * x ^ 2 + ρ ^ 2 / (1 - ρ) * y ^ 2 := by
  have h1' : 0 < 1 - ρ := by linarith
  have k2 : ρ * (x + y) ^ 2 ≤ x ^ 2 + ρ / (1 - ρ) * y ^ 2 := by
    rw [← sub_nonneg]
    have : x ^ 2 + ρ / (1 - ρ) * y ^ 2 - ρ * (x + y) ^ 2 = ((1 - ρ) * x - ρ * y) ^ 2 / (1 - ρ) := by
      field_simp; ring
    rw [this]; positivity
  calc ρ ^ 2 * (x + y) ^ 2 = ρ * (ρ * (x + y) ^ 2) := by ring
    _ ≤ ρ * (x ^ 2 + ρ / (1 - ρ) * y ^ 2) := mul_le_mul_of_nonneg_left k2 h0
    _ = _ := by ring

lemma young_inv {ρ x y : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) :
    (x + y) ^ 2 ≤ 1 / ρ * x ^ 2 + 1 / (1 - ρ) * y ^ 2 := by
  have h1' : 0 < 1 - ρ := by linarith
  have key : ρ * (1 - ρ) * (x + y) ^ 2 ≤ (1 - ρ) * x ^ 2 + ρ * y ^ 2 := by
    nlinarith [sq_nonneg ((1 - ρ) * x - ρ * y)]
  have e : 1 / ρ * x ^ 2 + 1 / (1 - ρ) * y ^ 2 = ((1 - ρ) * x ^ 2 + ρ * y ^ 2) / (ρ * (1 - ρ)) := by
    field_simp
  rw [e, le_div_iff₀ (mul_pos h0 h1')]
  linarith

lemma norm_add_sq_le_sq_add {d : ℕ} (a b : E d) : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2

lemma sum_add_le {n d : ℕ} {ρ S : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (a b : Fin n → E d)
    (hA : ∑ i, ‖a i‖ ^ 2 ≤ ρ ^ 2 * S) (hS : 0 ≤ S) :
    ∑ i, ‖a i + b i‖ ^ 2 ≤ ρ * S + 1 / (1 - ρ) * ∑ i, ‖b i‖ ^ 2 := by
  rcases h0.eq_or_lt with h | h
  · subst h
    have ha : ∀ i, a i = 0 := by
      intro i
      have hle : ‖a i‖ ^ 2 ≤ ∑ j, ‖a j‖ ^ 2 :=
        Finset.single_le_sum (f := fun j => ‖a j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      have : ‖a i‖ ^ 2 ≤ 0 := by simpa using le_trans hle hA
      have : ‖a i‖ = 0 := by nlinarith [norm_nonneg (a i)]
      exact norm_eq_zero.mp this
    simp [ha]
  · calc ∑ i, ‖a i + b i‖ ^ 2 ≤ ∑ i, (1 / ρ * ‖a i‖ ^ 2 + 1 / (1 - ρ) * ‖b i‖ ^ 2) :=
          Finset.sum_le_sum (fun i _ => le_trans (norm_add_sq_le_sq_add _ _) (young_inv h h1))
      _ = 1 / ρ * ∑ i, ‖a i‖ ^ 2 + 1 / (1 - ρ) * ∑ i, ‖b i‖ ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 1 / ρ * (ρ ^ 2 * S) + 1 / (1 - ρ) * ∑ i, ‖b i‖ ^ 2 := by
          gcongr
      _ = ρ * S + 1 / (1 - ρ) * ∑ i, ‖b i‖ ^ 2 := by field_simp

/-! ### Generic consensus estimates for one mixing step -/

/-- consensus error of `zᵢ = ∑ⱼ wᵢⱼ (xⱼ + γ tⱼ)`. -/
lemma mix_consensus {n d : ℕ} {W : Matrix (Fin n) (Fin n) ℝ} {ρ : ℝ} (h : Assumption22 W ρ)
    (γ : ℝ) (x t : Fin n → E d) :
    ∑ i, ‖(∑ j, W i j • (x j + γ • t j)) - avg (fun i => ∑ j, W i j • (x j + γ • t j))‖ ^ 2 ≤
      ρ * ∑ i, ‖x i - avg x‖ ^ 2 + ρ ^ 2 * γ ^ 2 / (1 - ρ) * ∑ i, ‖t i - avg t‖ ^ 2 := by
  rw [avg_mix h (fun j => x j + γ • t j)]
  have e0 : ∀ i, (∑ j, W i j • (x j + γ • t j)) - avg (fun j => x j + γ • t j) =
      ∑ j, W i j • ((x j + γ • t j) - avg (fun j => x j + γ • t j)) :=
    fun i => mix_sub_avg h (fun j => x j + γ • t j) _ i
  rw [Finset.sum_congr rfl (fun i _ => by rw [e0 i])]
  have hb := (lemmaA1 W ρ h (fun j => x j + γ • t j)).2
  refine le_trans hb ?_
  have hwbar : avg (fun j => x j + γ • t j) = avg x + γ • avg t := by
    rw [avg_add, avg_smul]
  have e : ∀ j, (x j + γ • t j) - avg (fun j => x j + γ • t j) =
      (x j - avg x) + γ • (t j - avg t) := by
    intro j; rw [hwbar]; simp only [smul_sub]; abel
  calc ρ ^ 2 * ∑ i, ‖(x i + γ • t i) - avg (fun j => x j + γ • t j)‖ ^ 2
      ≤ ∑ i, (ρ * ‖x i - avg x‖ ^ 2 + ρ ^ 2 / (1 - ρ) * (|γ| * ‖t i - avg t‖) ^ 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [e i]
        have h2 := norm_add_sq_le_sq_add (x i - avg x) (γ • (t i - avg t))
        rw [norm_smul, Real.norm_eq_abs] at h2
        exact le_trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg ρ)) (young_rho h.rho_nonneg h.rho_lt_one)
    _ = ρ * ∑ i, ‖x i - avg x‖ ^ 2 + ρ ^ 2 * γ ^ 2 / (1 - ρ) * ∑ i, ‖t i - avg t‖ ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        congr 1; refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [mul_pow, sq_abs]; ring

/-- tracker recursion `t'ᵢ = ∑ⱼ wᵢⱼ tⱼ + dᵢ − d'ᵢ`. -/
lemma tracker_avg {n d : ℕ} {W : Matrix (Fin n) (Fin n) ℝ} {ρ : ℝ} (h : Assumption22 W ρ)
    (t a b : Fin n → E d) :
    avg (fun i => ∑ j, W i j • t j + a i - b i) = avg t + avg a - avg b := by
  rw [avg_sub (fun i => ∑ j, W i j • t j + a i) b,
    avg_add (fun i => ∑ j, W i j • t j) a, avg_mix h]

lemma tracker_consensus {n d : ℕ} {W : Matrix (Fin n) (Fin n) ℝ} {ρ : ℝ} (h : Assumption22 W ρ)
    (t a b : Fin n → E d) :
    ∑ i, ‖(∑ j, W i j • t j + a i - b i) - avg (fun i => ∑ j, W i j • t j + a i - b i)‖ ^ 2 ≤
      ρ * ∑ i, ‖t i - avg t‖ ^ 2 + 1 / (1 - ρ) * ∑ i, ‖a i - b i‖ ^ 2 := by
  rw [tracker_avg h]
  have hδbar : avg (fun i => a i - b i) = avg a - avg b := avg_sub a b
  have e : ∀ i, (∑ j, W i j • t j + a i - b i) - (avg t + avg a - avg b) =
      (∑ j, W i j • (t j - avg t)) + ((a i - b i) - avg (fun i => a i - b i)) := by
    intro i; rw [← mix_sub_avg h t (avg t) i, hδbar]; abel
  rw [Finset.sum_congr rfl (fun i _ => by rw [e i])]
  have h1 := sum_add_le h.rho_nonneg h.rho_lt_one (fun i => ∑ j, W i j • (t j - avg t))
    (fun i => (a i - b i) - avg (fun i => a i - b i)) (lemmaA1 W ρ h t).2
    (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  refine le_trans h1 ?_
  have h1' : 0 ≤ 1 / (1 - ρ) := by have := h.rho_lt_one; apply div_nonneg <;> linarith
  have h2 := sum_sq_sub_avg_le_sum_sq (fun i => a i - b i)
  nlinarith

lemma four_sq {p q r s : ℝ} : (p + q + r + s) ^ 2 ≤ 4 * (p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2) := by
  nlinarith [sq_nonneg (p - q), sq_nonneg (p - r), sq_nonneg (p - s), sq_nonneg (q - r),
    sq_nonneg (q - s), sq_nonneg (r - s)]

/-- successive difference `zᵢ − xᵢ` for `zᵢ = ∑ⱼ wᵢⱼ (xⱼ + γ tⱼ)`. -/
lemma mix_diff {n d : ℕ} {W : Matrix (Fin n) (Fin n) ℝ} {ρ : ℝ} (h : Assumption22 W ρ)
    (γ : ℝ) (x t : Fin n → E d) :
    ∑ i, ‖(∑ j, W i j • (x j + γ • t j)) - x i‖ ^ 2 ≤
      8 * ∑ i, ‖x i - avg x‖ ^ 2 + 4 * γ ^ 2 * ∑ i, ‖t i - avg t‖ ^ 2 +
      4 * n * γ ^ 2 * ‖avg t‖ ^ 2 := by
  have e : ∀ i, (∑ j, W i j • (x j + γ • t j)) - x i =
      (∑ j, W i j • (x j - avg x)) + (-(x i - avg x)) + γ • (∑ j, W i j • (t j - avg t)) +
        γ • avg t := by
    intro i
    have h1 := mix_sub_avg h x (avg x) i
    have h2 := mix_sub_avg h t (avg t) i
    rw [← h1, ← h2]
    have h3 : ∑ j, W i j • (x j + γ • t j) = ∑ j, W i j • x j + γ • ∑ j, W i j • t j := by
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [smul_add, smul_comm]
    rw [h3, smul_sub]; abel
  simp_rw [e]
  have hA := (lemmaA1 W ρ h (fun j => x j - avg x)).1
  have hB := (lemmaA1 W ρ h (fun j => t j - avg t)).1
  calc ∑ i, ‖(∑ j, W i j • (x j - avg x)) + (-(x i - avg x)) + γ • (∑ j, W i j • (t j - avg t)) +
        γ • avg t‖ ^ 2
      ≤ ∑ i, 4 * (‖∑ j, W i j • (x j - avg x)‖ ^ 2 + ‖x i - avg x‖ ^ 2 +
          γ ^ 2 * ‖∑ j, W i j • (t j - avg t)‖ ^ 2 + γ ^ 2 * ‖avg t‖ ^ 2) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have h4 := norm_add₄_le (a := ∑ j, W i j • (x j - avg x)) (b := -(x i - avg x))
          (c := γ • (∑ j, W i j • (t j - avg t))) (d := γ • avg t)
        have h5 := pow_le_pow_left₀ (norm_nonneg _) h4 2
        refine le_trans h5 (le_trans four_sq (le_of_eq ?_))
        simp only [norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    _ = 4 * ∑ i, ‖∑ j, W i j • (x j - avg x)‖ ^ 2 + 4 * ∑ i, ‖x i - avg x‖ ^ 2 +
          4 * γ ^ 2 * ∑ i, ‖∑ j, W i j • (t j - avg t)‖ ^ 2 + 4 * n * γ ^ 2 * ‖avg t‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ _ := by nlinarith [sq_nonneg γ]

end DecBilevel.SLDBO.Aux

namespace DecBilevel.SLDBO.Aux
open DecBilevel.SLDBO Finset

section RunFacts
variable {n p q : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (F f : Fin n → E p → E q → ℝ)
  (α β η r : ℝ) (x0 : E p) (y0 v0 : E q)

lemma trX_eq (k : ℕ) : trX (run W F f α β η r x0 y0 v0) k = fun i =>
    ∑ j, W i j • (run W F f α β η r x0 y0 v0 k).tx j + dirX (run W F f α β η r x0 y0 v0) k i -
      (run W F f α β η r x0 y0 v0 k).dx i := rfl
lemma trY_eq (k : ℕ) : trY (run W F f α β η r x0 y0 v0) k = fun i =>
    ∑ j, W i j • (run W F f α β η r x0 y0 v0 k).ty j + dirY (run W F f α β η r x0 y0 v0) k i -
      (run W F f α β η r x0 y0 v0 k).dy i := rfl
lemma trV_eq (k : ℕ) : trV (run W F f α β η r x0 y0 v0) k = fun i =>
    ∑ j, W i j • (run W F f α β η r x0 y0 v0 k).tv j + dirV (run W F f α β η r x0 y0 v0) k i -
      (run W F f α β η r x0 y0 v0 k).dv i := rfl
lemma tx_succ (k : ℕ) : (run W F f α β η r x0 y0 v0 (k + 1)).tx =
    trX (run W F f α β η r x0 y0 v0) k := rfl
lemma ty_succ (k : ℕ) : (run W F f α β η r x0 y0 v0 (k + 1)).ty =
    trY (run W F f α β η r x0 y0 v0) k := rfl
lemma tv_succ (k : ℕ) : (run W F f α β η r x0 y0 v0 (k + 1)).tv =
    trV (run W F f α β η r x0 y0 v0) k := rfl
lemma dx_succ (k : ℕ) : (run W F f α β η r x0 y0 v0 (k + 1)).dx =
    dirX (run W F f α β η r x0 y0 v0) k := rfl
lemma dy_succ (k : ℕ) : (run W F f α β η r x0 y0 v0 (k + 1)).dy =
    dirY (run W F f α β η r x0 y0 v0) k := rfl
lemma dv_succ (k : ℕ) : (run W F f α β η r x0 y0 v0 (k + 1)).dv =
    dirV (run W F f α β η r x0 y0 v0) k := rfl
lemma x_succ (k : ℕ) : (run W F f α β η r x0 y0 v0 (k + 1)).x = fun i =>
    ∑ j, W i j • ((run W F f α β η r x0 y0 v0 k).x j + (-α) • trX (run W F f α β η r x0 y0 v0) k j) := by
  funext i; simp only [neg_smul, ← sub_eq_add_neg]; rfl
lemma y_succ (k : ℕ) : (run W F f α β η r x0 y0 v0 (k + 1)).y = fun i =>
    ∑ j, W i j • ((run W F f α β η r x0 y0 v0 k).y j + (-β) • trY (run W F f α β η r x0 y0 v0) k j) := by
  funext i; simp only [neg_smul, ← sub_eq_add_neg]; rfl
lemma v_succ (k : ℕ) : (run W F f α β η r x0 y0 v0 (k + 1)).v = fun i =>
    ballProj r (∑ j, W i j • ((run W F f α β η r x0 y0 v0 k).v j +
      η • trV (run W F f α β η r x0 y0 v0) k j)) := rfl

lemma v_norm_le (hr : 0 ≤ r) (hv0 : ‖v0‖ ≤ r) (k : ℕ) (i : Fin n) :
    ‖(run W F f α β η r x0 y0 v0 k).v i‖ ≤ r := by
  cases k with
  | zero => exact hv0
  | succ k => rw [v_succ]; exact ballProj_norm_le hr _

variable {W} {ρ : ℝ} (h : Assumption22 W ρ)
include h

/-- `t̄ᵏ = d̄ᵏ` and the averaged updates (25). -/
theorem eq25 (k : ℕ) :
    let s := run W F f α β η r x0 y0 v0
    avg (trX s k) = avg (dirX s k) ∧ avg (s (k + 1)).x = avg (s k).x - α • avg (dirX s k) ∧
    avg (trY s k) = avg (dirY s k) ∧ avg (s (k + 1)).y = avg (s k).y - β • avg (dirY s k) ∧
    avg (trV s k) = avg (dirV s k) := by
  intro s
  -- invariant: average tracker = average direction for the stored pair
  have inv : ∀ k, avg (s k).tx = avg (s k).dx ∧ avg (s k).ty = avg (s k).dy ∧
      avg (s k).tv = avg (s k).dv := by
    intro k
    induction k with
    | zero => exact ⟨rfl, rfl, rfl⟩
    | succ k ih =>
      refine ⟨?_, ?_, ?_⟩
      · rw [tx_succ, dx_succ, trX_eq, tracker_avg h, ih.1]; abel
      · rw [ty_succ, dy_succ, trY_eq, tracker_avg h, ih.2.1]; abel
      · rw [tv_succ, dv_succ, trV_eq, tracker_avg h, ih.2.2]; abel
  have hX : avg (trX s k) = avg (dirX s k) := by
    have := (inv (k + 1)).1; rwa [tx_succ, dx_succ] at this
  have hY : avg (trY s k) = avg (dirY s k) := by
    have := (inv (k + 1)).2.1; rwa [ty_succ, dy_succ] at this
  have hV : avg (trV s k) = avg (dirV s k) := by
    have := (inv (k + 1)).2.2; rwa [tv_succ, dv_succ] at this
  refine ⟨hX, ?_, hY, ?_, hV⟩
  · show avg (run W F f α β η r x0 y0 v0 (k + 1)).x = _
    rw [x_succ, avg_mix h (fun j => (s k).x j + (-α) • trX s k j), avg_add, avg_smul, hX,
      neg_smul, ← sub_eq_add_neg]
  · show avg (run W F f α β η r x0 y0 v0 (k + 1)).y = _
    rw [y_succ, avg_mix h (fun j => (s k).y j + (-β) • trY s k j), avg_add, avg_smul, hY,
      neg_smul, ← sub_eq_add_neg]

/-- Lemma A.3 (21). -/
theorem lemmaA3 (hr : 0 ≤ r) (k : ℕ) :
    let s := run W F f α β η r x0 y0 v0
    ∑ i, ‖(s (k + 1)).v i - avg (s (k + 1)).v‖ ^ 2 ≤
      ρ * ∑ i, ‖(s k).v i - avg (s k).v‖ ^ 2 +
      ρ ^ 2 * η ^ 2 / (1 - ρ) * ∑ i, ‖trV s k i - avg (trV s k)‖ ^ 2 := by
  intro s
  show ∑ i, ‖(run W F f α β η r x0 y0 v0 (k + 1)).v i -
    avg (run W F f α β η r x0 y0 v0 (k + 1)).v‖ ^ 2 ≤ _
  rw [v_succ]
  refine le_trans (lemmaA2 r hr _) ?_
  exact mix_consensus h η (s k).v (trV s k)

/-- Remark A.1 (22)–(23). -/
theorem remarkA1 (k : ℕ) :
    let s := run W F f α β η r x0 y0 v0
    (∑ i, ‖(s (k + 1)).x i - avg (s (k + 1)).x‖ ^ 2 ≤
      ρ * ∑ i, ‖(s k).x i - avg (s k).x‖ ^ 2 +
      ρ ^ 2 * α ^ 2 / (1 - ρ) * ∑ i, ‖trX s k i - avg (trX s k)‖ ^ 2) ∧
    (∑ i, ‖(s (k + 1)).y i - avg (s (k + 1)).y‖ ^ 2 ≤
      ρ * ∑ i, ‖(s k).y i - avg (s k).y‖ ^ 2 +
      ρ ^ 2 * β ^ 2 / (1 - ρ) * ∑ i, ‖trY s k i - avg (trY s k)‖ ^ 2) := by
  intro s
  constructor
  · show ∑ i, ‖(run W F f α β η r x0 y0 v0 (k + 1)).x i -
      avg (run W F f α β η r x0 y0 v0 (k + 1)).x‖ ^ 2 ≤ _
    rw [x_succ]
    have := mix_consensus h (-α) (s k).x (trX s k)
    rwa [neg_sq] at this
  · show ∑ i, ‖(run W F f α β η r x0 y0 v0 (k + 1)).y i -
      avg (run W F f α β η r x0 y0 v0 (k + 1)).y‖ ^ 2 ≤ _
    rw [y_succ]
    have := mix_consensus h (-β) (s k).y (trY s k)
    rwa [neg_sq] at this

/-- Lemma A.4 (24) and Remark A.2 (26)–(27). -/
theorem lemmaA4 (k : ℕ) :
    let s := run W F f α β η r x0 y0 v0
    (∑ i, ‖trX s (k + 1) i - avg (trX s (k + 1))‖ ^ 2 ≤
      ρ * ∑ i, ‖trX s k i - avg (trX s k)‖ ^ 2 +
      1 / (1 - ρ) * ∑ i, ‖dirX s (k + 1) i - dirX s k i‖ ^ 2) ∧
    (∑ i, ‖trV s (k + 1) i - avg (trV s (k + 1))‖ ^ 2 ≤
      ρ * ∑ i, ‖trV s k i - avg (trV s k)‖ ^ 2 +
      1 / (1 - ρ) * ∑ i, ‖dirV s (k + 1) i - dirV s k i‖ ^ 2) ∧
    (∑ i, ‖trY s (k + 1) i - avg (trY s (k + 1))‖ ^ 2 ≤
      ρ * ∑ i, ‖trY s k i - avg (trY s k)‖ ^ 2 +
      1 / (1 - ρ) * ∑ i, ‖dirY s (k + 1) i - dirY s k i‖ ^ 2) := by
  intro s
  refine ⟨?_, ?_, ?_⟩
  · have e : trX s (k + 1) = fun i => ∑ j, W i j • trX s k j + dirX s (k + 1) i - dirX s k i := by
      show trX (run W F f α β η r x0 y0 v0) (k + 1) = _
      rw [trX_eq, tx_succ, dx_succ]
    rw [e]; exact tracker_consensus h _ _ _
  · have e : trV s (k + 1) = fun i => ∑ j, W i j • trV s k j + dirV s (k + 1) i - dirV s k i := by
      show trV (run W F f α β η r x0 y0 v0) (k + 1) = _
      rw [trV_eq, tv_succ, dv_succ]
    rw [e]; exact tracker_consensus h _ _ _
  · have e : trY s (k + 1) = fun i => ∑ j, W i j • trY s k j + dirY s (k + 1) i - dirY s k i := by
      show trY (run W F f α β η r x0 y0 v0) (k + 1) = _
      rw [trY_eq, ty_succ, dy_succ]
    rw [e]; exact tracker_consensus h _ _ _

/-- Lemma A.6 (31). -/
theorem lemmaA6 (hr : 0 ≤ r) (hv0 : ‖v0‖ ≤ r) (k : ℕ) :
    let s := run W F f α β η r x0 y0 v0
    ∑ i, ‖(s (k + 1)).v i - (s k).v i‖ ^ 2 ≤
      8 * ∑ i, ‖(s k).v i - avg (s k).v‖ ^ 2 +
      4 * η ^ 2 * ∑ i, ‖trV s k i - avg (trV s k)‖ ^ 2 +
      4 * n * η ^ 2 * ‖avg (dirV s k)‖ ^ 2 := by
  intro s
  have hV := (eq25 F f α β η r x0 y0 v0 h k).2.2.2.2
  rw [← hV]
  refine le_trans ?_ (mix_diff h η (s k).v (trV s k))
  refine Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
  show ‖(run W F f α β η r x0 y0 v0 (k + 1)).v i - _‖ ≤ _
  rw [v_succ]
  have hb : ballProj r ((s k).v i) = (s k).v i := ballProj_of_le (v_norm_le W F f α β η r x0 y0 v0 hr hv0 k i)
  conv_lhs => rw [← hb]
  exact ballProj_nonexp hr _ _

/-- Remark A.3 (32)–(33). -/
theorem remarkA3 (k : ℕ) :
    let s := run W F f α β η r x0 y0 v0
    (∑ i, ‖(s (k + 1)).x i - (s k).x i‖ ^ 2 ≤
      8 * ∑ i, ‖(s k).x i - avg (s k).x‖ ^ 2 +
      4 * α ^ 2 * ∑ i, ‖trX s k i - avg (trX s k)‖ ^ 2 +
      4 * n * α ^ 2 * ‖avg (dirX s k)‖ ^ 2) ∧
    (∑ i, ‖(s (k + 1)).y i - (s k).y i‖ ^ 2 ≤
      8 * ∑ i, ‖(s k).y i - avg (s k).y‖ ^ 2 +
      4 * β ^ 2 * ∑ i, ‖trY s k i - avg (trY s k)‖ ^ 2 +
      4 * n * β ^ 2 * ‖avg (dirY s k)‖ ^ 2) := by
  intro s
  have H := eq25 F f α β η r x0 y0 v0 h k
  constructor
  · rw [← H.1]
    show ∑ i, ‖(run W F f α β η r x0 y0 v0 (k + 1)).x i - _‖ ^ 2 ≤ _
    rw [x_succ]
    have := mix_diff h (-α) (s k).x (trX s k)
    rwa [neg_sq] at this
  · rw [← H.2.2.1]
    show ∑ i, ‖(run W F f α β η r x0 y0 v0 (k + 1)).y i - _‖ ^ 2 ≤ _
    rw [y_succ]
    have := mix_diff h (-β) (s k).y (trY s k)
    rwa [neg_sq] at this

end RunFacts

end DecBilevel.SLDBO.Aux

namespace DecBilevel.SLDBO.Calc
open DecBilevel.SLDBO Finset InnerProductSpace

/-! ### Strong convexity: gradient inequality and strong monotonicity -/

lemma sc_grad_ineq {d : ℕ} {g : E d → ℝ} {σ : ℝ} (hg : StrongConvexOn Set.univ σ g)
    {G y : E d} (hG : HasGradientAt g G y) (z : E d) :
    g y + inner ℝ G (z - y) + σ / 2 * ‖z - y‖ ^ 2 ≤ g z := by
  have hφ : HasDerivAt (fun t : ℝ => g (y + t • (z - y))) (inner ℝ G (z - y)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => y + t • (z - y)) (z - y) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const (z - y)).const_add y
    have h2 : HasFDerivAt g (toDual ℝ (E d) G) (y + (0:ℝ) • (z - y)) := by
      simpa using hG.hasFDerivAt
    have h3 := h2.comp_hasDerivAt (0:ℝ) h1
    rw [InnerProductSpace.toDual_apply_apply] at h3
    exact h3
  have hlim := hφ.tendsto_slope_zero_right
  have hR : Filter.Tendsto (fun t : ℝ => g z - g y - (1 - t) * (σ / 2) * ‖z - y‖ ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (g z - g y - (1 - 0) * (σ / 2) * ‖z - y‖ ^ 2)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    exact ((continuous_const.sub ((continuous_const.sub continuous_id).mul continuous_const
      |>.mul continuous_const)).tendsto 0)
  have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      t⁻¹ • (g (y + (0 + t) • (z - y)) - g (y + (0:ℝ) • (z - y))) ≤
        g z - g y - (1 - t) * (σ / 2) * ‖z - y‖ ^ 2 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have hc := hg.2 (Set.mem_univ y) (Set.mem_univ z) (show (0:ℝ) ≤ 1 - t by linarith) ht0.le
      (by ring)
    have e : (1 - t) • y + t • z = y + t • (z - y) := by
      rw [sub_smul, one_smul, smul_sub]; abel
    rw [e, smul_eq_mul, smul_eq_mul, norm_sub_rev y z] at hc
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
    rw [inv_mul_le_iff₀ ht0]
    nlinarith
  have := le_of_tendsto_of_tendsto hlim hR hev
  linarith

lemma sc_mono {d : ℕ} {g : E d → ℝ} {σ : ℝ} (hg : StrongConvexOn Set.univ σ g)
    {Gy Gz y z : E d} (hy : HasGradientAt g Gy y) (hz : HasGradientAt g Gz z) :
    σ * ‖y - z‖ ^ 2 ≤ inner ℝ (Gy - Gz) (y - z) := by
  have h1 := sc_grad_ineq hg hy z
  have h2 := sc_grad_ineq hg hz y
  have e1 : z - y = -(y - z) := by abel
  rw [e1, inner_neg_right, norm_neg] at h1
  rw [inner_sub_left]
  linarith

end DecBilevel.SLDBO.Calc

namespace DecBilevel.SLDBO.Calc
open DecBilevel.SLDBO Finset InnerProductSpace

section Partial
variable {p q : ℕ} {g : E p → E q → ℝ}

lemma hasGrad2 (hg : Differentiable ℝ (fun z : E p × E q => g z.1 z.2)) (x : E p) (y : E q) :
    HasGradientAt (fun y' => g x y') (grad2 g x y) y := by
  have : DifferentiableAt ℝ (fun y' => g x y') y :=
    (hg (x, y)).comp y ((differentiableAt_const x).prodMk differentiableAt_id)
  exact this.hasGradientAt

lemma hasGrad1 (hg : Differentiable ℝ (fun z : E p × E q => g z.1 z.2)) (x : E p) (y : E q) :
    HasGradientAt (fun x' => g x' y) (grad1 g x y) x := by
  have : DifferentiableAt ℝ ((fun z : E p × E q => g z.1 z.2) ∘ (fun x' => (x', y))) x :=
    (hg (x, y)).comp x ((hasFDerivAt_prodMk_left (𝕜 := ℝ) x y).differentiableAt)
  exact this.hasGradientAt

lemma grad2_apply (hg : Differentiable ℝ (fun z : E p × E q => g z.1 z.2)) (x : E p) (y : E q)
    (c : Fin q) : grad2 g x y c =
      fderiv ℝ (fun z : E p × E q => g z.1 z.2) (x, y) (0, EuclideanSpace.single c 1) := by
  have h1 : HasFDerivAt (fun y' => g x y')
      ((fderiv ℝ (fun z : E p × E q => g z.1 z.2) (x, y)).comp
        (ContinuousLinearMap.inr ℝ (E p) (E q))) y :=
    (hg (x, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right x y)
  have h2 : grad2 g x y c = inner ℝ (grad2 g x y) (EuclideanSpace.single c 1) := by
    rw [real_inner_comm, EuclideanSpace.inner_single_left]; simp
  rw [h2, grad2, inner_gradient_left, h1.fderiv]
  rfl

lemma grad1_apply (hg : Differentiable ℝ (fun z : E p × E q => g z.1 z.2)) (x : E p) (y : E q)
    (c : Fin p) : grad1 g x y c =
      fderiv ℝ (fun z : E p × E q => g z.1 z.2) (x, y) (EuclideanSpace.single c 1, 0) := by
  have h1 : HasFDerivAt ((fun z : E p × E q => g z.1 z.2) ∘ (fun x' => (x', y)))
      ((fderiv ℝ (fun z : E p × E q => g z.1 z.2) (x, y)).comp
        (ContinuousLinearMap.inl ℝ (E p) (E q))) x :=
    (hg (x, y)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y)
  have h2 : grad1 g x y c = inner ℝ (grad1 g x y) (EuclideanSpace.single c 1) := by
    rw [real_inner_comm, EuclideanSpace.inner_single_left]; simp
  rw [h2, grad1, inner_gradient_left]
  have h1' : HasFDerivAt (fun x' => g x' y)
      ((fderiv ℝ (fun z : E p × E q => g z.1 z.2) (x, y)).comp
        (ContinuousLinearMap.inl ℝ (E p) (E q))) x := h1
  rw [h1'.fderiv]
  rfl

lemma grad2_contDiff (hg : ContDiff ℝ 2 (fun z : E p × E q => g z.1 z.2)) :
    ContDiff ℝ 1 (fun z : E p × E q => grad2 g z.1 z.2) := by
  have hd : Differentiable ℝ (fun z : E p × E q => g z.1 z.2) := hg.differentiable (by norm_num)
  rw [contDiff_euclidean]; intro c
  have e : (fun z : E p × E q => grad2 g z.1 z.2 c) = fun z =>
      fderiv ℝ (fun z : E p × E q => g z.1 z.2) z (0, EuclideanSpace.single c 1) := by
    funext z; exact grad2_apply hd z.1 z.2 c
  rw [e]
  exact (hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

lemma grad1_contDiff (hg : ContDiff ℝ 2 (fun z : E p × E q => g z.1 z.2)) :
    ContDiff ℝ 1 (fun z : E p × E q => grad1 g z.1 z.2) := by
  have hd : Differentiable ℝ (fun z : E p × E q => g z.1 z.2) := hg.differentiable (by norm_num)
  rw [contDiff_euclidean]; intro c
  have e : (fun z : E p × E q => grad1 g z.1 z.2 c) = fun z =>
      fderiv ℝ (fun z : E p × E q => g z.1 z.2) z (EuclideanSpace.single c 1, 0) := by
    funext z; exact grad1_apply hd z.1 z.2 c
  rw [e]
  exact (hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

lemma grad2_diffY (hg : ContDiff ℝ 2 (fun z : E p × E q => g z.1 z.2)) (x : E p) (y : E q) :
    HasFDerivAt (fun y' => grad2 g x y') (hess22 g x y) y := by
  have : DifferentiableAt ℝ (fun y' => grad2 g x y') y :=
    ((grad2_contDiff hg).differentiable (by norm_num) (x, y)).comp y
      ((differentiableAt_const x).prodMk differentiableAt_id)
  exact this.hasFDerivAt

lemma grad1_diffY (hg : ContDiff ℝ 2 (fun z : E p × E q => g z.1 z.2)) (x : E p) (y : E q) :
    HasFDerivAt (fun y' => grad1 g x y') (hess12 g x y) y := by
  have : DifferentiableAt ℝ (fun y' => grad1 g x y') y :=
    ((grad1_contDiff hg).differentiable (by norm_num) (x, y)).comp y
      ((differentiableAt_const x).prodMk differentiableAt_id)
  exact this.hasFDerivAt

/-- Hessian lower bound from strong convexity. -/
lemma hess22_coercive {σ : ℝ} (hg : ContDiff ℝ 2 (fun z : E p × E q => g z.1 z.2)) (x : E p)
    (hsc : StrongConvexOn Set.univ σ (g x)) (y u : E q) :
    σ * ‖u‖ ^ 2 ≤ inner ℝ (hess22 g x y u) u := by
  have hd : Differentiable ℝ (fun z : E p × E q => g z.1 z.2) := hg.differentiable (by norm_num)
  have hline : HasDerivAt (fun t : ℝ => y + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const u).const_add y
  have hG : HasFDerivAt (fun y' => grad2 g x y') (hess22 g x y) (y + (0:ℝ) • u) := by
    simpa using grad2_diffY hg x y
  have hψ : HasDerivAt (fun t : ℝ => inner ℝ (grad2 g x (y + t • u)) u)
      (inner ℝ (hess22 g x y u) u) 0 := by
    have h1 := hG.comp_hasDerivAt (0:ℝ) hline
    have h2 := h1.inner ℝ (hasDerivAt_const (0:ℝ) u)
    simpa using h2
  have hlim := hψ.tendsto_slope_zero_right
  have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      σ * ‖u‖ ^ 2 ≤ t⁻¹ • (inner ℝ (grad2 g x (y + (0 + t) • u)) u -
        inner ℝ (grad2 g x (y + (0:ℝ) • u)) u) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0:ℝ) < t := ht
    have hm := sc_mono hsc (hasGrad2 hd x (y + t • u)) (hasGrad2 hd x y)
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0,
      inner_smul_right] at hm
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
    rw [le_inv_mul_iff₀ ht0]
    have e : σ * (t * ‖u‖) ^ 2 = t * (t * (σ * ‖u‖ ^ 2)) := by ring
    have h3 : t * (t * (σ * ‖u‖ ^ 2)) ≤
        t * (inner ℝ (grad2 g x (y + t • u)) u - inner ℝ (grad2 g x y) u) := by
      rw [← inner_sub_left]; linarith
    exact le_of_mul_le_mul_left h3 ht0
  exact ge_of_tendsto hlim hev

end Partial

/-! ### Coercive operators -/

lemma coercive_lower {d : ℕ} {σ : ℝ} (hσ : 0 < σ) (H : E d →L[ℝ] E d)
    (hc : ∀ u, σ * ‖u‖ ^ 2 ≤ inner ℝ (H u) u) (u : E d) : σ * ‖u‖ ≤ ‖H u‖ := by
  have h1 := hc u
  have h2 : inner ℝ (H u) u ≤ ‖H u‖ * ‖u‖ := real_inner_le_norm _ _
  rcases (norm_nonneg u).eq_or_lt with h0 | h0
  · rw [← h0]; simp
  · nlinarith

lemma coercive_inverse {d : ℕ} {σ : ℝ} (hσ : 0 < σ) (H : E d →L[ℝ] E d)
    (hc : ∀ u, σ * ‖u‖ ^ 2 ≤ inner ℝ (H u) u) (w : E d) : H (H.inverse w) = w := by
  have inj : Function.Injective H.toLinearMap := by
    intro a b hab
    have : H (a - b) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr hab
    have h := coercive_lower hσ H hc (a - b)
    rw [this, norm_zero] at h
    have : ‖a - b‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (a - b)]) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  let e := (LinearEquiv.ofInjectiveEndo H.toLinearMap inj).toContinuousLinearEquiv
  have he : (e : E d →L[ℝ] E d) = H := by ext v; rfl
  rw [← he, ContinuousLinearMap.inverse_equiv]
  exact e.apply_symm_apply w

end DecBilevel.SLDBO.Calc

namespace DecBilevel.SLDBO.Calc
open DecBilevel.SLDBO Finset InnerProductSpace

lemma fst_le_sqrt {a b : ℝ} (ha : 0 ≤ a) : a ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
  have := Real.abs_le_sqrt (x := a) (y := a ^ 2 + b ^ 2) (by nlinarith [sq_nonneg b])
  rwa [abs_of_nonneg ha] at this

lemma snd_le_sqrt {a b : ℝ} (hb : 0 ≤ b) : b ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [add_comm]; exact fst_le_sqrt hb

section PD
variable {p q : ℕ}
lemma pdist_le (x x' : E p) (y y' : E q) : pdist x x' y y' ≤ ‖x - x'‖ + ‖y - y'‖ := by
  unfold pdist
  rw [Real.sqrt_le_left]
  · nlinarith [norm_nonneg (x - x'), norm_nonneg (y - y')]
  · positivity

lemma pdist_same_x (x : E p) (y y' : E q) : pdist x x y y' = ‖y - y'‖ := by
  simp [pdist, Real.sqrt_sq (norm_nonneg _)]

lemma pdist_same_y (x x' : E p) (y : E q) : pdist x x' y y = ‖x - x'‖ := by
  simp [pdist, Real.sqrt_sq (norm_nonneg _)]

lemma pdist_nonneg (x x' : E p) (y y' : E q) : 0 ≤ pdist x x' y y' := Real.sqrt_nonneg _
end PD

lemma avg_norm_sub_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ} (hn : 0 < n)
    (a b : Fin n → V) {L : ℝ} (h : ∀ i, ‖a i - b i‖ ≤ L) :
    ‖(1 / (n : ℝ)) • ∑ i, a i - (1 / (n : ℝ)) • ∑ i, b i‖ ≤ L := by
  rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  calc 1 / (n:ℝ) * ‖∑ i, (a i - b i)‖ ≤ 1 / (n:ℝ) * ∑ i, ‖a i - b i‖ := by
        gcongr; exact norm_sum_le _ _
    _ ≤ 1 / (n:ℝ) * ∑ _i : Fin n, L := by gcongr with i; exact h i
    _ = L := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp

lemma avg_norm_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ} (hn : 0 < n)
    (a : Fin n → V) {L : ℝ} (h : ∀ i, ‖a i‖ ≤ L) : ‖(1 / (n : ℝ)) • ∑ i, a i‖ ≤ L := by
  have := avg_norm_sub_le hn a (fun _ => 0) (L := L) (by simpa using h)
  simpa using this

section Setting
variable {n p q : ℕ} {F f : Fin n → E p → E q → ℝ} {σ LF0 LF1 Lf1 Lf2 : ℝ}
  (hA : Assumption21 F f σ LF0 LF1 Lf1 Lf2)
include hA

lemma fdiff (i : Fin n) : Differentiable ℝ (fun z : E p × E q => f i z.1 z.2) :=
  (hA.f_contDiff i).differentiable (by norm_num)

lemma grad2f_lip (i : Fin n) (x x' : E p) (y y' : E q) :
    ‖grad2 (f i) x y - grad2 (f i) x' y'‖ ≤ Lf1 * pdist x x' y y' :=
  le_trans (snd_le_sqrt (norm_nonneg _)) (hA.gradf_lip i x x' y y')

lemma grad1f_lip (i : Fin n) (x x' : E p) (y y' : E q) :
    ‖grad1 (f i) x y - grad1 (f i) x' y'‖ ≤ Lf1 * pdist x x' y y' :=
  le_trans (fst_le_sqrt (norm_nonneg _)) (hA.gradf_lip i x x' y y')

lemma grad2F_lip (i : Fin n) (x x' : E p) (y y' : E q) :
    ‖grad2 (F i) x y - grad2 (F i) x' y'‖ ≤ LF1 * pdist x x' y y' :=
  le_trans (snd_le_sqrt (norm_nonneg _)) (hA.gradF_lip i x x' y y')

lemma grad1F_lip (i : Fin n) (x x' : E p) (y y' : E q) :
    ‖grad1 (F i) x y - grad1 (F i) x' y'‖ ≤ LF1 * pdist x x' y y' :=
  le_trans (fst_le_sqrt (norm_nonneg _)) (hA.gradF_lip i x x' y y')

lemma grad2F_norm (i : Fin n) (x : E p) (y : E q) : ‖grad2 (F i) x y‖ ≤ LF0 := by
  rw [grad2, gradient, LinearIsometryEquiv.norm_map]
  apply norm_fderiv_le_of_lip' ℝ hA.LF0_nonneg
  filter_upwards with y'
  have := hA.F_lip i x x y' y
  rw [pdist_same_x, ← Real.norm_eq_abs] at this
  exact this

lemma grad1F_norm (i : Fin n) (x : E p) (y : E q) : ‖grad1 (F i) x y‖ ≤ LF0 := by
  rw [grad1, gradient, LinearIsometryEquiv.norm_map]
  apply norm_fderiv_le_of_lip' ℝ hA.LF0_nonneg
  filter_upwards with x'
  have := hA.F_lip i x' x y y
  rw [pdist_same_y, ← Real.norm_eq_abs] at this
  exact this

lemma hess12_norm (i : Fin n) (x : E p) (y : E q) : ‖hess12 (f i) x y‖ ≤ Lf1 := by
  rw [hess12]
  apply norm_fderiv_le_of_lip' ℝ hA.Lf1_nonneg
  filter_upwards with y'
  have := grad1f_lip hA i x x y' y
  rwa [pdist_same_x] at this

lemma hess22_norm (i : Fin n) (x : E p) (y : E q) : ‖hess22 (f i) x y‖ ≤ Lf1 := by
  rw [hess22]
  apply norm_fderiv_le_of_lip' ℝ hA.Lf1_nonneg
  filter_upwards with y'
  have := grad2f_lip hA i x x y' y
  rwa [pdist_same_x] at this

variable (hn : 0 < n)
include hn

lemma avgGrad2f_lip (x x' : E p) (y y' : E q) :
    ‖avgGrad2 f x y - avgGrad2 f x' y'‖ ≤ Lf1 * pdist x x' y y' :=
  avg_norm_sub_le hn _ _ (fun i => grad2f_lip hA i x x' y y')

lemma avgGrad2F_lip (x x' : E p) (y y' : E q) :
    ‖avgGrad2 F x y - avgGrad2 F x' y'‖ ≤ LF1 * pdist x x' y y' :=
  avg_norm_sub_le hn _ _ (fun i => grad2F_lip hA i x x' y y')

lemma avgGrad1F_lip (x x' : E p) (y y' : E q) :
    ‖avgGrad1 F x y - avgGrad1 F x' y'‖ ≤ LF1 * pdist x x' y y' :=
  avg_norm_sub_le hn _ _ (fun i => grad1F_lip hA i x x' y y')

lemma avgHess22_lip (x x' : E p) (y y' : E q) :
    ‖avgHess22 f x y - avgHess22 f x' y'‖ ≤ Lf2 * pdist x x' y y' :=
  avg_norm_sub_le hn _ _ (fun i => hA.hess22_lip i x x' y y')

lemma avgHess12_lip (x x' : E p) (y y' : E q) :
    ‖avgHess12 f x y - avgHess12 f x' y'‖ ≤ Lf2 * pdist x x' y y' :=
  avg_norm_sub_le hn _ _ (fun i => hA.hess12_lip i x x' y y')

lemma avgGrad2F_norm (x : E p) (y : E q) : ‖avgGrad2 F x y‖ ≤ LF0 :=
  avg_norm_le hn _ (fun i => grad2F_norm hA i x y)

lemma avgHess12_norm (x : E p) (y : E q) : ‖avgHess12 f x y‖ ≤ Lf1 :=
  avg_norm_le hn _ (fun i => hess12_norm hA i x y)

lemma avgHess22_norm (x : E p) (y : E q) : ‖avgHess22 f x y‖ ≤ Lf1 :=
  avg_norm_le hn _ (fun i => hess22_norm hA i x y)

lemma avgGrad2f_mono (x : E p) (y z : E q) :
    σ * ‖y - z‖ ^ 2 ≤ inner ℝ (avgGrad2 f x y - avgGrad2 f x z) (y - z) := by
  have hi : ∀ i, σ * ‖y - z‖ ^ 2 ≤ inner ℝ (grad2 (f i) x y - grad2 (f i) x z) (y - z) :=
    fun i => sc_mono (hA.strongConvex i x) (hasGrad2 (fdiff hA i) x y) (hasGrad2 (fdiff hA i) x z)
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have e : inner ℝ (avgGrad2 f x y - avgGrad2 f x z) (y - z) =
      1 / (n:ℝ) * ∑ i, inner ℝ (grad2 (f i) x y - grad2 (f i) x z) (y - z) := by
    unfold avgGrad2
    rw [← smul_sub, ← Finset.sum_sub_distrib, real_inner_smul_left, sum_inner]
  rw [e]
  calc σ * ‖y - z‖ ^ 2 = 1 / (n:ℝ) * ∑ _i : Fin n, σ * ‖y - z‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
    _ ≤ _ := by gcongr with i; exact hi i

lemma avgHess22_coercive (x : E p) (y u : E q) :
    σ * ‖u‖ ^ 2 ≤ inner ℝ (avgHess22 f x y u) u := by
  have hi : ∀ i, σ * ‖u‖ ^ 2 ≤ inner ℝ (hess22 (f i) x y u) u :=
    fun i => hess22_coercive (hA.f_contDiff i) x (hA.strongConvex i x) y u
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have e : inner ℝ (avgHess22 f x y u) u = 1 / (n:ℝ) * ∑ i, inner ℝ (hess22 (f i) x y u) u := by
    rw [avgHess22, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
      real_inner_smul_left, sum_inner]
  rw [e]
  calc σ * ‖u‖ ^ 2 = 1 / (n:ℝ) * ∑ _i : Fin n, σ * ‖u‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
    _ ≤ _ := by gcongr with i; exact hi i

lemma hasGrad_avgf (x : E p) (y : E q) : HasGradientAt (avgf f x) (avgGrad2 f x y) y := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hs : HasFDerivAt (fun y' => ∑ i, f i x y') (∑ i, toDual ℝ (E q) (grad2 (f i) x y)) y :=
    HasFDerivAt.fun_sum (fun i _ => (hasGrad2 (fdiff hA i) x y).hasFDerivAt)
  have := hs.const_mul (1 / (n:ℝ))
  refine this.congr_fderiv ?_
  unfold avgGrad2
  rw [map_smulₛₗ, map_sum]
  simp

variable {ystar : E p → E q} (hys : ∀ x, IsMinOn (avgf f x) Set.univ (ystar x))
include hys

lemma ystar_stat (x : E p) : avgGrad2 f x (ystar x) = 0 := by
  have hmin : IsLocalMin (avgf f x) (ystar x) := (hys x).isLocalMin Filter.univ_mem
  have h := hmin.hasFDerivAt_eq_zero (hasGrad_avgf hA hn x (ystar x)).hasFDerivAt
  exact (LinearIsometryEquiv.map_eq_zero_iff _).mp h

theorem ystar_lip (x x' : E p) : ‖ystar x - ystar x'‖ ≤ Lf1 / σ * ‖x - x'‖ := by
  have hσ := hA.sigma_pos
  have hm := avgGrad2f_mono hA hn x' (ystar x) (ystar x')
  rw [ystar_stat hA hn hys x', sub_zero, ← sub_zero (avgGrad2 f x' (ystar x)),
    ← ystar_stat hA hn hys x] at hm
  have hl := avgGrad2f_lip hA hn x' x (ystar x) (ystar x)
  rw [pdist_same_y] at hl
  have h2 := real_inner_le_norm (avgGrad2 f x' (ystar x) - avgGrad2 f x (ystar x))
    (ystar x - ystar x')
  have h3 : σ * ‖ystar x - ystar x'‖ ^ 2 ≤ Lf1 * ‖x' - x‖ * ‖ystar x - ystar x'‖ :=
    le_trans hm (le_trans h2 (mul_le_mul_of_nonneg_right hl (norm_nonneg _)))
  rw [norm_sub_rev x' x] at h3
  rw [div_mul_eq_mul_div, le_div_iff₀ hσ]
  rcases (norm_nonneg (ystar x - ystar x')).eq_or_lt with h0 | h0
  · rw [← h0, zero_mul]; have := hA.Lf1_nonneg; positivity
  · nlinarith

omit hys in
lemma vstar_eq (x : E p) :
    avgHess22 f x (ystar x) (vstar F f ystar x) = avgGrad2 F x (ystar x) :=
  coercive_inverse hA.sigma_pos _ (avgHess22_coercive hA hn x (ystar x)) _

lemma vstar_norm (x : E p) : ‖vstar F f ystar x‖ ≤ rv σ LF0 := by
  have hσ := hA.sigma_pos
  have h1 := coercive_lower hσ _ (avgHess22_coercive hA hn x (ystar x)) (vstar F f ystar x)
  rw [vstar_eq (F := F) (ystar := ystar) hA hn x] at h1
  have h2 := avgGrad2F_norm hA hn x (ystar x)
  rw [rv, le_div_iff₀ hσ]; linarith

lemma pdist_ystar_le (x x' : E p) :
    pdist x x' (ystar x) (ystar x') ≤ (1 + Lf1 / σ) * ‖x - x'‖ := by
  have := pdist_le x x' (ystar x) (ystar x')
  have := ystar_lip hA hn hys x x'
  nlinarith

theorem vstar_lip (x x' : E p) :
    ‖vstar F f ystar x - vstar F f ystar x'‖ ≤ Lv σ LF0 LF1 Lf1 Lf2 / σ * ‖x - x'‖ := by
  have hσ := hA.sigma_pos
  set H := avgHess22 f x (ystar x)
  set H' := avgHess22 f x' (ystar x')
  set v := vstar F f ystar x
  set v' := vstar F f ystar x'
  have hv := vstar_eq (F := F) (ystar := ystar) hA hn x
  have hv' := vstar_eq (F := F) (ystar := ystar) hA hn x'
  have e : H (v - v') = (avgGrad2 F x (ystar x) - avgGrad2 F x' (ystar x')) + (H' v' - H v') := by
    rw [map_sub, hv, ← hv']; abel
  have h1 := coercive_lower hσ H (avgHess22_coercive hA hn x (ystar x)) (v - v')
  rw [e] at h1
  have hP := pdist_ystar_le hA hn hys x x'
  have hP0 := pdist_nonneg x x' (ystar x) (ystar x')
  have hg := avgGrad2F_lip hA hn x x' (ystar x) (ystar x')
  have hH : ‖H' v' - H v'‖ ≤ Lf2 * pdist x x' (ystar x) (ystar x') * rv σ LF0 := by
    rw [← sub_apply]
    refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
    rw [norm_sub_rev]
    exact mul_le_mul (avgHess22_lip hA hn x x' (ystar x) (ystar x')) (vstar_norm hA hn hys x')
      (norm_nonneg _) (mul_nonneg hA.Lf2_nonneg hP0)
  have h2 : σ * ‖v - v'‖ ≤ (LF1 + Lf2 * rv σ LF0) * pdist x x' (ystar x) (ystar x') := by
    have := norm_add_le (avgGrad2 F x (ystar x) - avgGrad2 F x' (ystar x')) (H' v' - H v')
    nlinarith
  have hL1 : 0 ≤ LF1 + Lf2 * rv σ LF0 := by
    have := hA.LF1_nonneg; have := hA.Lf2_nonneg
    have : 0 ≤ rv σ LF0 := div_nonneg hA.LF0_nonneg hσ.le
    positivity
  rw [Lv, L1, div_mul_eq_mul_div, le_div_iff₀ hσ]
  have := mul_le_mul_of_nonneg_left hP hL1
  nlinarith

theorem hypergrad_lip (x x' : E p) :
    ‖hypergrad F f ystar x - hypergrad F f ystar x'‖ ≤ LPhi σ LF0 LF1 Lf1 Lf2 * ‖x - x'‖ := by
  have hσ := hA.sigma_pos
  have hP := pdist_ystar_le hA hn hys x x'
  have hP0 := pdist_nonneg x x' (ystar x) (ystar x')
  set A := avgHess12 f x (ystar x)
  set A' := avgHess12 f x' (ystar x')
  set v := vstar F f ystar x
  set v' := vstar F f ystar x'
  have e : hypergrad F f ystar x - hypergrad F f ystar x' =
      (avgGrad1 F x (ystar x) - avgGrad1 F x' (ystar x')) - (A (v - v') + (A - A') v') := by
    simp only [hypergrad, A, A', v, v', map_sub, sub_apply]; abel
  rw [e]
  have h1 := avgGrad1F_lip hA hn x x' (ystar x) (ystar x')
  have h2 : ‖A (v - v')‖ ≤ Lf1 * (Lv σ LF0 LF1 Lf1 Lf2 / σ * ‖x - x'‖) :=
    le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_mul (avgHess12_norm hA hn x (ystar x)) (vstar_lip hA hn hys x x') (norm_nonneg _)
        hA.Lf1_nonneg)
  have h3 : ‖(A - A') v'‖ ≤ Lf2 * pdist x x' (ystar x) (ystar x') * rv σ LF0 :=
    le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_mul (avgHess12_lip hA hn x x' (ystar x) (ystar x')) (vstar_norm hA hn hys x')
        (norm_nonneg _) (mul_nonneg hA.Lf2_nonneg hP0))
  have h4 := norm_sub_le (avgGrad1 F x (ystar x) - avgGrad1 F x' (ystar x'))
    (A (v - v') + (A - A') v')
  have h5 := norm_add_le (A (v - v')) ((A - A') v')
  have hrv : 0 ≤ rv σ LF0 := div_nonneg hA.LF0_nonneg hσ.le
  have hL1 : 0 ≤ LF1 + Lf2 * rv σ LF0 := by
    have := hA.LF1_nonneg; have := hA.Lf2_nonneg; positivity
  -- combine: (LF1 + Lf2 rv) P + Lf1 Lv/σ ‖Δx‖ ≤ LPhi ‖Δx‖
  have hP' := mul_le_mul_of_nonneg_left hP hL1
  have key : LPhi σ LF0 LF1 Lf1 Lf2 * ‖x - x'‖ =
      (LF1 + Lf2 * rv σ LF0) * ((1 + Lf1 / σ) * ‖x - x'‖) +
        Lf1 * (Lv σ LF0 LF1 Lf1 Lf2 / σ * ‖x - x'‖) := by
    rw [LPhi, Lv, L1]; field_simp
  rw [key]
  nlinarith

end Setting
end DecBilevel.SLDBO.Calc

namespace DecBilevel.SLDBO.Calc
open DecBilevel.SLDBO Finset InnerProductSpace

section Second
variable {p q : ℕ} {g : E p → E q → ℝ}

lemma inner_grad2_eq (hd : Differentiable ℝ (fun z : E p × E q => g z.1 z.2)) (z : E p × E q)
    (w : E q) : inner ℝ (grad2 g z.1 z.2) w = fderiv ℝ (fun z : E p × E q => g z.1 z.2) z (0, w) := by
  have h1 : HasFDerivAt (fun y' => g z.1 y')
      ((fderiv ℝ (fun z : E p × E q => g z.1 z.2) (z.1, z.2)).comp
        (ContinuousLinearMap.inr ℝ (E p) (E q))) z.2 :=
    (hd (z.1, z.2)).hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right z.1 z.2)
  rw [grad2, inner_gradient_left, h1.fderiv]
  rfl

lemma inner_grad1_eq (hd : Differentiable ℝ (fun z : E p × E q => g z.1 z.2)) (z : E p × E q)
    (h : E p) : inner ℝ (grad1 g z.1 z.2) h = fderiv ℝ (fun z : E p × E q => g z.1 z.2) z (h, 0) := by
  have h1 : HasFDerivAt ((fun z : E p × E q => g z.1 z.2) ∘ (fun x' => (x', z.2)))
      ((fderiv ℝ (fun z : E p × E q => g z.1 z.2) (z.1, z.2)).comp
        (ContinuousLinearMap.inl ℝ (E p) (E q))) z.1 :=
    (hd (z.1, z.2)).hasFDerivAt.comp z.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)
  have h1' : HasFDerivAt (fun x' => g x' z.2)
      ((fderiv ℝ (fun z : E p × E q => g z.1 z.2) (z.1, z.2)).comp
        (ContinuousLinearMap.inl ℝ (E p) (E q))) z.1 := h1
  rw [grad1, inner_gradient_left, h1'.fderiv]
  rfl

/-- Generic: if `Γ` has derivative `M` at `z0` and `⟪Γ z, w⟫ = (Df z) c` for all `z`,
then `⟪M v, w⟫ = D²f z0 v c`. -/
lemma inner_deriv_eq {d : ℕ} (hg : ContDiff ℝ 2 (fun z : E p × E q => g z.1 z.2))
    (Γ : E p × E q → E d) (z0 : E p × E q) (hΓ : DifferentiableAt ℝ Γ z0) (w : E d)
    (c : E p × E q) (hc : ∀ z, inner ℝ (Γ z) w = fderiv ℝ (fun z : E p × E q => g z.1 z.2) z c)
    (v : E p × E q) :
    inner ℝ (fderiv ℝ Γ z0 v) w =
      fderiv ℝ (fderiv ℝ (fun z : E p × E q => g z.1 z.2)) z0 v c := by
  have hD : DifferentiableAt ℝ (fderiv ℝ (fun z : E p × E q => g z.1 z.2)) z0 :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z0
  have h1 : HasFDerivAt (fun z => inner ℝ w (Γ z)) ((innerSL ℝ w).comp (fderiv ℝ Γ z0)) z0 :=
    (innerSL ℝ w).hasFDerivAt.comp z0 hΓ.hasFDerivAt
  have h2 : HasFDerivAt (fun z => fderiv ℝ (fun z : E p × E q => g z.1 z.2) z c)
      ((fderiv ℝ (fun z : E p × E q => g z.1 z.2) z0).comp 0 +
        (fderiv ℝ (fderiv ℝ (fun z : E p × E q => g z.1 z.2)) z0).flip c) z0 :=
    hD.hasFDerivAt.clm_apply (hasFDerivAt_const c z0)
  have e : (fun z => inner ℝ w (Γ z)) = fun z => fderiv ℝ (fun z : E p × E q => g z.1 z.2) z c := by
    funext z; rw [real_inner_comm, hc]
  rw [e] at h1
  have := congrArg (fun L => L v) (h1.unique h2)
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, innerSL_apply_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.zero_apply, map_zero,
    ContinuousLinearMap.flip_apply, zero_add] at this
  rw [real_inner_comm]; exact this

variable (hg : ContDiff ℝ 2 (fun z : E p × E q => g z.1 z.2))
include hg

lemma symm2 (z0 : E p × E q) (a b : E p × E q) :
    fderiv ℝ (fderiv ℝ (fun z : E p × E q => g z.1 z.2)) z0 a b =
      fderiv ℝ (fderiv ℝ (fun z : E p × E q => g z.1 z.2)) z0 b a :=
  (hg.contDiffAt.isSymmSndFDerivAt (by simp)) a b

lemma Γ2_diff (z0 : E p × E q) : DifferentiableAt ℝ (fun z : E p × E q => grad2 g z.1 z.2) z0 :=
  (grad2_contDiff hg).differentiable (by norm_num) z0

lemma Γ1_diff (z0 : E p × E q) : DifferentiableAt ℝ (fun z : E p × E q => grad1 g z.1 z.2) z0 :=
  (grad1_contDiff hg).differentiable (by norm_num) z0

lemma hess22_eq (x : E p) (y : E q) (u : E q) :
    hess22 g x y u = fderiv ℝ (fun z : E p × E q => grad2 g z.1 z.2) (x, y) (0, u) := by
  have h1 : HasFDerivAt (fun y' => grad2 g x y')
      ((fderiv ℝ (fun z : E p × E q => grad2 g z.1 z.2) (x, y)).comp
        (ContinuousLinearMap.inr ℝ (E p) (E q))) y :=
    (Γ2_diff hg (x, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right x y)
  rw [hess22, h1.fderiv]; rfl

lemma hess12_eq (x : E p) (y : E q) (u : E q) :
    hess12 g x y u = fderiv ℝ (fun z : E p × E q => grad1 g z.1 z.2) (x, y) (0, u) := by
  have h1 : HasFDerivAt (fun y' => grad1 g x y')
      ((fderiv ℝ (fun z : E p × E q => grad1 g z.1 z.2) (x, y)).comp
        (ContinuousLinearMap.inr ℝ (E p) (E q))) y :=
    (Γ1_diff hg (x, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right x y)
  rw [hess12, h1.fderiv]; rfl

lemma hess22_symm (x : E p) (y : E q) (u w : E q) :
    inner ℝ (hess22 g x y u) w = inner ℝ u (hess22 g x y w) := by
  have hd : Differentiable ℝ (fun z : E p × E q => g z.1 z.2) := hg.differentiable (by norm_num)
  rw [hess22_eq hg, hess22_eq hg,
    real_inner_comm (fderiv ℝ (fun z : E p × E q => grad2 g z.1 z.2) (x, y) (0, w)) u,
    inner_deriv_eq hg _ (x, y) (Γ2_diff hg _) w (0, w) (fun z => inner_grad2_eq hd z w),
    inner_deriv_eq hg _ (x, y) (Γ2_diff hg _) u (0, u) (fun z => inner_grad2_eq hd z u)]
  exact symm2 hg _ _ _

/-- the mixed identity `⟪∂ₓ∇₂g · h, w⟫ = ⟪∇²₁₂g · w, h⟫`. -/
lemma mixed_symm (x : E p) (y : E q) (h : E p) (w : E q) :
    inner ℝ (fderiv ℝ (fun z : E p × E q => grad2 g z.1 z.2) (x, y) (h, 0)) w =
      inner ℝ (hess12 g x y w) h := by
  have hd : Differentiable ℝ (fun z : E p × E q => g z.1 z.2) := hg.differentiable (by norm_num)
  rw [hess12_eq hg,
    inner_deriv_eq hg _ (x, y) (Γ2_diff hg _) w (0, w) (fun z => inner_grad2_eq hd z w),
    inner_deriv_eq hg _ (x, y) (Γ1_diff hg _) h (h, 0) (fun z => inner_grad1_eq hd z h)]
  exact symm2 hg _ _ _

end Second

end DecBilevel.SLDBO.Calc

namespace DecBilevel.SLDBO.Calc
open DecBilevel.SLDBO Finset InnerProductSpace Asymptotics Filter Topology

lemma coercive_equiv {d : ℕ} {σ : ℝ} (hσ : 0 < σ) (H : E d →L[ℝ] E d)
    (hc : ∀ u, σ * ‖u‖ ^ 2 ≤ inner ℝ (H u) u) : ∃ e : E d ≃L[ℝ] E d, (e : E d →L[ℝ] E d) = H := by
  have inj : Function.Injective H.toLinearMap := by
    intro a b hab
    have : H (a - b) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr hab
    have h := coercive_lower hσ H hc (a - b)
    rw [this, norm_zero] at h
    have : ‖a - b‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (a - b)]) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  exact ⟨(LinearEquiv.ofInjectiveEndo H.toLinearMap inj).toContinuousLinearEquiv, by ext v; rfl⟩

section Hyper
variable {n p q : ℕ} {F f : Fin n → E p → E q → ℝ} {σ LF0 LF1 Lf1 Lf2 : ℝ}
  (hA : Assumption21 F f σ LF0 LF1 Lf1 Lf2) (hn : 0 < n)
  {ystar : E p → E q} (hys : ∀ x, IsMinOn (avgf f x) Set.univ (ystar x))
include hA hn

/-- derivative of the averaged lower-level gradient map. -/
lemma avgΓ_hasFDerivAt (z0 : E p × E q) :
    HasFDerivAt (fun z : E p × E q => avgGrad2 f z.1 z.2)
      ((1 / (n : ℝ)) • ∑ i, fderiv ℝ (fun z : E p × E q => grad2 (f i) z.1 z.2) z0) z0 := by
  have hs : HasFDerivAt (fun z : E p × E q => ∑ i, grad2 (f i) z.1 z.2)
      (∑ i, fderiv ℝ (fun z : E p × E q => grad2 (f i) z.1 z.2) z0) z0 :=
    HasFDerivAt.fun_sum (fun i _ => (Γ2_diff (hA.f_contDiff i) z0).hasFDerivAt)
  exact hs.const_smul (1 / (n : ℝ))

lemma avgM_inr (x : E p) (y u : E q) :
    ((1 / (n : ℝ)) • ∑ i, fderiv ℝ (fun z : E p × E q => grad2 (f i) z.1 z.2) (x, y)) (0, u) =
      avgHess22 f x y u := by
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, avgHess22]
  congr 1; refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hess22_eq (hA.f_contDiff i)]

lemma avgM_inl (x : E p) (y : E q) (h : E p) (w : E q) :
    inner ℝ (((1 / (n : ℝ)) • ∑ i, fderiv ℝ (fun z : E p × E q => grad2 (f i) z.1 z.2) (x, y))
      (h, 0)) w = inner ℝ (avgHess12 f x y w) h := by
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, avgHess12,
    real_inner_smul_left, sum_inner]
  congr 1; refine Finset.sum_congr rfl (fun i _ => ?_)
  exact mixed_symm (hA.f_contDiff i) x y h w

lemma avgHess22_symm (x : E p) (y u w : E q) :
    inner ℝ (avgHess22 f x y u) w = inner ℝ u (avgHess22 f x y w) := by
  simp only [avgHess22, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    real_inner_smul_left, real_inner_smul_right, sum_inner, inner_sum]
  congr 1; refine Finset.sum_congr rfl (fun i _ => ?_)
  exact hess22_symm (hA.f_contDiff i) x y u w

include hys

theorem eq7 (x : E p) : HasGradientAt (Phi F ystar) (hypergrad F f ystar x) x := by
  have hσ := hA.sigma_pos
  set y0 := ystar x with hy0
  set M := (1 / (n : ℝ)) • ∑ i, fderiv ℝ (fun z : E p × E q => grad2 (f i) z.1 z.2) (x, y0)
  set H := avgHess22 f x y0
  obtain ⟨e, he⟩ := coercive_equiv hσ H (avgHess22_coercive hA hn x y0)
  set J : E p →L[ℝ] E q := M.comp (ContinuousLinearMap.inl ℝ (E p) (E q))
  set D : E p →L[ℝ] E q := -((e.symm : E q →L[ℝ] E q).comp J)
  have hMinr : ∀ u, M (0, u) = H u := fun u => avgM_inr hA hn x y0 u
  have hMsplit : ∀ h u, M (h, u) = J h + H u := by
    intro h u
    have : ((h, u) : E p × E q) = (h, 0) + (0, u) := by simp
    rw [this, map_add, hMinr]; rfl
  -- Step 1: derivative of `ystar`
  have hY : HasFDerivAt ystar D x := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    have hΓ := (avgΓ_hasFDerivAt hA hn (x, y0))
    rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hΓ
    set φ : E p → E p × E q := fun h => (h, ystar (x + h) - ystar x)
    have hcont : Continuous ystar := by
      apply LipschitzWith.continuous (K := ⟨Lf1 / σ, div_nonneg hA.Lf1_nonneg hσ.le⟩)
      apply LipschitzWith.of_dist_le_mul
      intro a b
      rw [dist_eq_norm, dist_eq_norm]
      exact ystar_lip hA hn hys a b
    have hφ : Tendsto φ (𝓝 0) (𝓝 0) := by
      have : Continuous φ := continuous_id.prodMk
        ((hcont.comp (continuous_const.add continuous_id)).sub continuous_const)
      have h0 : φ 0 = 0 := by simp [φ]
      rw [← h0]; exact this.tendsto 0
    have h1 := hΓ.comp_tendsto hφ
    have h1' : (fun h => M (φ h)) =o[𝓝 0] φ := by
      have := h1.neg_left
      refine this.congr_left (fun h => ?_)
      have e1 : avgGrad2 f (x + h) (y0 + (ystar (x + h) - ystar x)) = 0 := by
        rw [hy0, add_sub_cancel]; exact ystar_stat hA hn hys _
      have e2 : avgGrad2 f x y0 = 0 := ystar_stat hA hn hys x
      simp only [Function.comp_apply, φ, Prod.fst_add, Prod.snd_add, e1, e2]
      abel
    have h2 : φ =O[𝓝 0] (fun h => h) := by
      apply IsBigO.of_bound (max 1 (Lf1 / σ))
      filter_upwards with h
      rw [Prod.norm_def]
      have hl := ystar_lip hA hn hys (x + h) x
      rw [add_sub_cancel_left] at hl
      apply max_le
      · exact le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _)
      · exact le_trans hl (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
    have h3 := ((e.symm : E q →L[ℝ] E q).isBigO_comp (fun h => M (φ h)) (𝓝 0)).trans_isLittleO
      (h1'.trans_isBigO h2)
    refine h3.congr_left (fun h => ?_)
    show e.symm (M (φ h)) = ystar (x + h) - ystar x - D h
    rw [hMsplit, map_add]
    have : e.symm (H (ystar (x + h) - ystar x)) = ystar (x + h) - ystar x := by
      rw [← he]; exact e.symm_apply_apply _
    rw [this]
    simp only [D, ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearEquiv.coe_coe, sub_neg_eq_add]
    abel
  -- Step 2: chain rule for Φ
  have hψ : HasFDerivAt (fun x' => (x', ystar x')) ((ContinuousLinearMap.id ℝ (E p)).prod D) x :=
    (hasFDerivAt_id x).prodMk hY
  have hFi : ∀ i, HasFDerivAt (fun x' => F i x' (ystar x'))
      ((fderiv ℝ (fun z : E p × E q => F i z.1 z.2) (x, y0)).comp
        ((ContinuousLinearMap.id ℝ (E p)).prod D)) x :=
    fun i => by
      have := ((hA.F_diff i) (x, y0)).hasFDerivAt.comp x hψ
      exact this
  have hΦ := (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hFi i)).const_mul (1 / (n : ℝ))
  rw [hasGradientAt_iff_hasFDerivAt]
  refine hΦ.congr_fderiv ?_
  ext h
  simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_id', id_eq, smul_eq_mul]
  have hsplit : ∀ i, fderiv ℝ (fun z : E p × E q => F i z.1 z.2) (x, y0) (h, D h) =
      inner ℝ (grad1 (F i) x y0) h + inner ℝ (grad2 (F i) x y0) (D h) := by
    intro i
    have : ((h, D h) : E p × E q) = (h, 0) + (0, D h) := by simp
    rw [this, map_add, inner_grad1_eq (hA.F_diff i) (x, y0) h,
      inner_grad2_eq (hA.F_diff i) (x, y0) (D h)]
  simp only [hsplit, Finset.sum_add_distrib, mul_add]
  -- the y-part: ⟪avgGrad2 F, D h⟫ = -⟪avgHess12 v*, h⟫
  have hg : (1 / (n : ℝ)) * ∑ i, inner ℝ (grad2 (F i) x y0) (D h) =
      inner ℝ (avgGrad2 F x y0) (D h) := by
    rw [avgGrad2, real_inner_smul_left, sum_inner]
  have hf1 : (1 / (n : ℝ)) * ∑ i, inner ℝ (grad1 (F i) x y0) h = inner ℝ (avgGrad1 F x y0) h := by
    rw [avgGrad1, real_inner_smul_left, sum_inner]
  rw [hg, hf1]
  have hv : vstar F f ystar x = e.symm (avgGrad2 F x y0) := by
    rw [vstar, ← hy0]; show H.inverse _ = _; rw [← he, ContinuousLinearMap.inverse_equiv]; rfl
  have key : inner ℝ (avgGrad2 F x y0) (D h) = -inner ℝ (avgHess12 f x y0 (vstar F f ystar x)) h := by
    set a := e.symm (avgGrad2 F x y0)
    set b := e.symm (J h)
    have ha : H a = avgGrad2 F x y0 := by rw [← he]; exact e.apply_symm_apply _
    have hb : H b = J h := by rw [← he]; exact e.apply_symm_apply _
    have hDh : D h = -b := rfl
    rw [hDh, inner_neg_right, ← ha, avgHess22_symm hA hn, hb, hv, real_inner_comm]
    congr 1
    exact avgM_inl hA hn x y0 h a
  rw [key, hypergrad, inner_sub_left, ← hy0]
  ring

end Hyper
end DecBilevel.SLDBO.Calc

namespace DecBilevel.SLDBO.Gen
open DecBilevel.SLDBO Finset InnerProductSpace

/-- descent lemma for an `L`-smooth function. -/
lemma descent {d : ℕ} {φ : E d → ℝ} {G : E d → E d} {L : ℝ}
    (hG : ∀ x, HasGradientAt φ (G x) x) (hL : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (x Δ : E d) :
    φ (x + Δ) ≤ φ x + inner ℝ (G x) Δ + L / 2 * ‖Δ‖ ^ 2 := by
  set h : ℝ → ℝ := fun t => φ (x + t • Δ) - t * inner ℝ (G x) Δ - L / 2 * t ^ 2 * ‖Δ‖ ^ 2
  have hd : ∀ t, HasDerivAt h (inner ℝ (G (x + t • Δ)) Δ - inner ℝ (G x) Δ - L * t * ‖Δ‖ ^ 2) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • Δ) Δ t := by
      simpa using ((hasDerivAt_id t).smul_const Δ).const_add x
    have h2 := (hG (x + t • Δ)).hasFDerivAt.comp_hasDerivAt t h1
    rw [InnerProductSpace.toDual_apply_apply] at h2
    have h3 := ((hasDerivAt_id t).mul_const (inner ℝ (G x) Δ))
    have h4 := (((hasDerivAt_id t).pow 2).const_mul (L / 2)).mul_const (‖Δ‖ ^ 2)
    have := (h2.sub h3).sub h4
    have e1 : (((φ ∘ fun t => x + t • Δ) - fun y => id y * inner ℝ (G x) Δ) -
        fun y => L / 2 * (id ^ 2) y * ‖Δ‖ ^ 2) = h := by
      funext s; simp [h]
    rw [e1] at this
    refine this.congr_deriv ?_
    simp only [id, one_mul, mul_one, Nat.cast_ofNat, pow_one, Nat.add_one_sub_one]
    ring
  have hmono : AntitoneOn h (Set.Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
    · exact (fun t _ => (hd t).continuousAt.continuousWithinAt)
    · intro t _; exact (hd t).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht0 : 0 ≤ t := ht.1.le
      have e1 : inner ℝ (G (x + t • Δ)) Δ - inner ℝ (G x) Δ = inner ℝ (G (x + t • Δ) - G x) Δ :=
        (inner_sub_left _ _ _).symm
      have e2 := real_inner_le_norm (G (x + t • Δ) - G x) Δ
      have e3 := hL (x + t • Δ) x
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0] at e3
      have : ‖G (x + t • Δ) - G x‖ * ‖Δ‖ ≤ L * (t * ‖Δ‖) * ‖Δ‖ :=
        mul_le_mul_of_nonneg_right e3 (norm_nonneg _)
      nlinarith
  have := hmono (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one) zero_le_one
  simp only [h, one_smul, zero_smul, add_zero, one_mul, zero_mul, sub_zero, one_pow,
    mul_one] at this
  norm_num at this
  linarith

/-- `‖(G' − B' v') − (G − B v)‖ ≤ (a + b r) P + c ‖v' − v‖`. -/
lemma pair_bound {V U : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup U]
    [NormedSpace ℝ U] (G G' : V) (B B' : U →L[ℝ] V) (v v' : U) {a b c r P : ℝ}
    (hG : ‖G' - G‖ ≤ a * P) (hB : ‖B' - B‖ ≤ b * P) (hBn : ‖B‖ ≤ c) (hv' : ‖v'‖ ≤ r)
    (hP : 0 ≤ P) (hb : 0 ≤ b) :
    ‖(G' - B' v') - (G - B v)‖ ≤ (a + b * r) * P + c * ‖v' - v‖ := by
  have e : (G' - B' v') - (G - B v) = (G' - G) - ((B' - B) v' + B (v' - v)) := by
    simp only [sub_apply, map_sub]; abel
  rw [e]
  have h1 := norm_sub_le (G' - G) ((B' - B) v' + B (v' - v))
  have h2 := norm_add_le ((B' - B) v') (B (v' - v))
  have h3 : ‖(B' - B) v'‖ ≤ b * P * r :=
    le_trans (ContinuousLinearMap.le_opNorm _ _) (mul_le_mul hB hv' (norm_nonneg _)
      (mul_nonneg hb hP))
  have h4 : ‖B (v' - v)‖ ≤ c * ‖v' - v‖ :=
    le_trans (ContinuousLinearMap.le_opNorm _ _) (mul_le_mul_of_nonneg_right hBn (norm_nonneg _))
  nlinarith

lemma sq_add_le_two {a b : ℝ} : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

lemma sq_add4_le {a b c d : ℝ} : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

lemma norm_add_sq_young {V : Type*} [NormedAddCommGroup V] (u b : V) {ξ : ℝ} (hξ : 0 < ξ) :
    ‖u + b‖ ^ 2 ≤ (1 + ξ) * ‖u‖ ^ 2 + (1 + 1 / ξ) * ‖b‖ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le u b) 2
  have : (‖u‖ + ‖b‖) ^ 2 ≤ (1 + ξ) * ‖u‖ ^ 2 + (1 + 1 / ξ) * ‖b‖ ^ 2 := by
    have key : 0 ≤ (ξ * ‖u‖ - ‖b‖) ^ 2 / ξ := by positivity
    have : (1 + ξ) * ‖u‖ ^ 2 + (1 + 1 / ξ) * ‖b‖ ^ 2 - (‖u‖ + ‖b‖) ^ 2 =
        (ξ * ‖u‖ - ‖b‖) ^ 2 / ξ := by field_simp; ring
    linarith
  linarith

/-- Jensen: `‖(1/n) ∑ aᵢ‖² ≤ (1/n) ∑ ‖aᵢ‖²`. -/
lemma norm_avg_sq_le {d n : ℕ} (hn : 0 < n) (a : Fin n → E d) :
    ‖(1 / (n : ℝ)) • ∑ i, a i‖ ^ 2 ≤ (1 / (n : ℝ)) * ∑ i, ‖a i‖ ^ 2 := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have h := Aux.norm_sq_wsum_le (fun _ => 1 / (n : ℝ)) (fun _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp) a
  rw [Finset.smul_sum, ← Finset.mul_sum] at *
  exact h

/-- `‖c − z̄‖² ≤ (1/n)∑‖c − zᵢ‖²`-type: `‖avg z − c‖² ≤ (1/n) ∑ ‖zᵢ − c‖²`. -/
lemma norm_avg_sub_sq_le {d n : ℕ} (hn : 0 < n) (z : Fin n → E d) (c : E d) :
    ‖avg z - c‖ ^ 2 ≤ (1 / (n : ℝ)) * ∑ i, ‖z i - c‖ ^ 2 := by
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have e : avg z - c = (1 / (n : ℝ)) • ∑ i, (z i - c) := by
    rw [Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, one_div_mul_cancel hn', one_smul]; rfl
  rw [e]; exact norm_avg_sq_le hn _

/-- `∑‖zᵢ − c‖² = ∑‖zᵢ − z̄‖² + n‖z̄ − c‖²`. -/
lemma sum_sq_sub_eq {d n : ℕ} (z : Fin n → E d) (c : E d) :
    ∑ i, ‖z i - c‖ ^ 2 = ∑ i, ‖z i - avg z‖ ^ 2 + n * ‖avg z - c‖ ^ 2 := by
  have key : ∀ i, ‖z i - c‖ ^ 2 =
      ‖z i - avg z‖ ^ 2 + 2 * inner ℝ (z i - avg z) (avg z - c) + ‖avg z - c‖ ^ 2 := by
    intro i
    have : z i - c = (z i - avg z) + (avg z - c) := by abel
    rw [this, norm_add_sq_real]
  simp_rw [key, Finset.sum_add_distrib, ← Finset.mul_sum, ← sum_inner, Aux.sum_sub_avg]
  simp [Finset.sum_const, Finset.card_univ]

end DecBilevel.SLDBO.Gen

namespace DecBilevel.SLDBO.Main
open DecBilevel.SLDBO Finset InnerProductSpace

lemma pdist_sq {p q : ℕ} (x x' : E p) (y y' : E q) :
    pdist x x' y y' ^ 2 = ‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- generic averaged error for `Gᵢ − Bᵢ v` families. -/
lemma avg_err {n p q d : ℕ} (hn : 0 < n) (Gf : Fin n → E p → E q → E d)
    (Bf : Fin n → E p → E q → (E q →L[ℝ] E d)) {a b c r : ℝ} (hb : 0 ≤ b)
    (hGl : ∀ i x x' y y', ‖Gf i x y - Gf i x' y'‖ ≤ a * pdist x x' y y')
    (hBl : ∀ i x x' y y', ‖Bf i x y - Bf i x' y'‖ ≤ b * pdist x x' y y')
    (hBn : ∀ i x y, ‖Bf i x y‖ ≤ c)
    (xs : Fin n → E p) (ys vs : Fin n → E q) (hvs : ∀ i, ‖vs i‖ ≤ r)
    (xh : E p) (yh vh : E q) :
    ‖(1 / (n : ℝ)) • ∑ i, (Gf i (xs i) (ys i) - Bf i (xs i) (ys i) (vs i)) -
        (1 / (n : ℝ)) • ∑ i, (Gf i xh yh - Bf i xh yh vh)‖ ^ 2 ≤
      (1 / (n : ℝ)) * ∑ i, ((a + b * r) * pdist (xs i) xh (ys i) yh + c * ‖vs i - vh‖) ^ 2 := by
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  refine le_trans (Gen.norm_avg_sq_le hn _) ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum; intro i _
  exact pow_le_pow_left₀ (norm_nonneg _) (Gen.pair_bound (Gf i xh yh) (Gf i (xs i) (ys i))
    (Bf i xh yh) (Bf i (xs i) (ys i)) vh (vs i) (hGl i _ _ _ _) (hBl i _ _ _ _) (hBn i _ _) (hvs i)
      (Calc.pdist_nonneg _ _ _ _) hb) 2

section RunBounds
variable {n p q : ℕ} {W : Matrix (Fin n) (Fin n) ℝ} {F f : Fin n → E p → E q → ℝ}
  {σ LF0 LF1 Lf1 Lf2 ρ α β η : ℝ} {x0 : E p} {y0 v0 : E q}

/-- normalized consensus error -/
noncomputable def cons {m d : ℕ} (z : Fin m → E d) : ℝ := (1 / (m : ℝ)) * ∑ i, ‖z i - avg z‖ ^ 2
/-- normalized squared successive difference -/
noncomputable def dsq {m d : ℕ} (z z' : Fin m → E d) : ℝ := (1 / (m : ℝ)) * ∑ i, ‖z' i - z i‖ ^ 2

lemma cons_nonneg {m d : ℕ} (z : Fin m → E d) : 0 ≤ cons z := by unfold cons; positivity
lemma dsq_nonneg {m d : ℕ} (z z' : Fin m → E d) : 0 ≤ dsq z z' := by unfold dsq; positivity

variable (hA : Assumption21 F f σ LF0 LF1 Lf1 Lf2) (hn : 0 < n)
include hA

lemma rv_nonneg : 0 ≤ rv σ LF0 := div_nonneg hA.LF0_nonneg hA.sigma_pos.le

lemma L1_nonneg : 0 ≤ LF1 + Lf2 * rv σ LF0 := by
  have := hA.LF1_nonneg; have := hA.Lf2_nonneg; have := rv_nonneg hA; positivity

include hn

/-- Lemma A.5 (with constant `2(L₁² + L_{f,1}²)`). -/
lemma dir_diff (k : ℕ) (hv0 : ‖v0‖ ≤ rv σ LF0) :
    let s := run W F f α β η (rv σ LF0) x0 y0 v0
    let Cd := 2 * ((LF1 + Lf2 * rv σ LF0) ^ 2 + Lf1 ^ 2)
    let DD := dsq (s k).x (s (k + 1)).x + dsq (s k).y (s (k + 1)).y + dsq (s k).v (s (k + 1)).v
    (1 / (n : ℝ)) * ∑ i, ‖dirX s (k + 1) i - dirX s k i‖ ^ 2 ≤ Cd * DD ∧
    (1 / (n : ℝ)) * ∑ i, ‖dirY s (k + 1) i - dirY s k i‖ ^ 2 ≤ Cd * DD ∧
    (1 / (n : ℝ)) * ∑ i, ‖dirV s (k + 1) i - dirV s k i‖ ^ 2 ≤ Cd * DD := by
  intro s Cd DD
  have hr := rv_nonneg hA
  have hL1 := L1_nonneg hA
  have hvle : ∀ i, ‖(s (k + 1)).v i‖ ≤ rv σ LF0 :=
    fun i => Aux.v_norm_le W F f α β η _ x0 y0 v0 hr hv0 (k + 1) i
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  -- per-agent bound for the `G − B v` directions
  have key : ∀ (Gf : Fin n → E p → E q → E p) (Bf : Fin n → E p → E q → (E q →L[ℝ] E p)),
      (∀ i x x' y y', ‖Gf i x y - Gf i x' y'‖ ≤ LF1 * pdist x x' y y') →
      (∀ i x x' y y', ‖Bf i x y - Bf i x' y'‖ ≤ Lf2 * pdist x x' y y') →
      (∀ i x y, ‖Bf i x y‖ ≤ Lf1) → ∀ i,
      ‖(Gf i ((s (k + 1)).x i) ((s (k + 1)).y i) -
          Bf i ((s (k + 1)).x i) ((s (k + 1)).y i) ((s (k + 1)).v i)) -
        (Gf i ((s k).x i) ((s k).y i) - Bf i ((s k).x i) ((s k).y i) ((s k).v i))‖ ^ 2 ≤
      Cd * (‖(s (k + 1)).x i - (s k).x i‖ ^ 2 + ‖(s (k + 1)).y i - (s k).y i‖ ^ 2 +
        ‖(s (k + 1)).v i - (s k).v i‖ ^ 2) := by
    intro Gf Bf hGl hBl hBn i
    have h := Gen.pair_bound (Gf i ((s k).x i) ((s k).y i))
      (Gf i ((s (k + 1)).x i) ((s (k + 1)).y i)) (Bf i ((s k).x i) ((s k).y i))
      (Bf i ((s (k + 1)).x i) ((s (k + 1)).y i)) ((s k).v i) ((s (k + 1)).v i)
      (hGl i _ _ _ _) (hBl i _ _ _ _) (hBn i ((s k).x i) ((s k).y i))
      (hvle i) (Calc.pdist_nonneg _ _ _ _) hA.Lf2_nonneg
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    refine le_trans h2 (le_trans Gen.sq_add_le_two ?_)
    rw [mul_pow, mul_pow, pdist_sq]
    have := sq_nonneg Lf1; have := sq_nonneg (LF1 + Lf2 * rv σ LF0)
    simp only [Cd]; nlinarith [sq_nonneg ‖(s (k + 1)).x i - (s k).x i‖,
      sq_nonneg ‖(s (k + 1)).y i - (s k).y i‖, sq_nonneg ‖(s (k + 1)).v i - (s k).v i‖]
  have keyq : ∀ (Gf : Fin n → E p → E q → E q) (Bf : Fin n → E p → E q → (E q →L[ℝ] E q)),
      (∀ i x x' y y', ‖Gf i x y - Gf i x' y'‖ ≤ LF1 * pdist x x' y y') →
      (∀ i x x' y y', ‖Bf i x y - Bf i x' y'‖ ≤ Lf2 * pdist x x' y y') →
      (∀ i x y, ‖Bf i x y‖ ≤ Lf1) → ∀ i,
      ‖(Gf i ((s (k + 1)).x i) ((s (k + 1)).y i) -
          Bf i ((s (k + 1)).x i) ((s (k + 1)).y i) ((s (k + 1)).v i)) -
        (Gf i ((s k).x i) ((s k).y i) - Bf i ((s k).x i) ((s k).y i) ((s k).v i))‖ ^ 2 ≤
      Cd * (‖(s (k + 1)).x i - (s k).x i‖ ^ 2 + ‖(s (k + 1)).y i - (s k).y i‖ ^ 2 +
        ‖(s (k + 1)).v i - (s k).v i‖ ^ 2) := by
    intro Gf Bf hGl hBl hBn i
    have h := Gen.pair_bound (Gf i ((s k).x i) ((s k).y i))
      (Gf i ((s (k + 1)).x i) ((s (k + 1)).y i)) (Bf i ((s k).x i) ((s k).y i))
      (Bf i ((s (k + 1)).x i) ((s (k + 1)).y i)) ((s k).v i) ((s (k + 1)).v i)
      (hGl i _ _ _ _) (hBl i _ _ _ _) (hBn i ((s k).x i) ((s k).y i))
      (hvle i) (Calc.pdist_nonneg _ _ _ _) hA.Lf2_nonneg
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    refine le_trans h2 (le_trans Gen.sq_add_le_two ?_)
    rw [mul_pow, mul_pow, pdist_sq]
    have := sq_nonneg Lf1; have := sq_nonneg (LF1 + Lf2 * rv σ LF0)
    simp only [Cd]; nlinarith [sq_nonneg ‖(s (k + 1)).x i - (s k).x i‖,
      sq_nonneg ‖(s (k + 1)).y i - (s k).y i‖, sq_nonneg ‖(s (k + 1)).v i - (s k).v i‖]
  have hsum : ∀ (u : Fin n → ℝ), (∀ i, u i ≤ Cd * (‖(s (k + 1)).x i - (s k).x i‖ ^ 2 +
      ‖(s (k + 1)).y i - (s k).y i‖ ^ 2 + ‖(s (k + 1)).v i - (s k).v i‖ ^ 2)) →
      (1 / (n : ℝ)) * ∑ i, u i ≤ Cd * DD := by
    intro u hu
    have : (1 / (n : ℝ)) * ∑ i, u i ≤ (1 / (n : ℝ)) * ∑ i, Cd * (‖(s (k + 1)).x i - (s k).x i‖ ^ 2 +
      ‖(s (k + 1)).y i - (s k).y i‖ ^ 2 + ‖(s (k + 1)).v i - (s k).v i‖ ^ 2) := by
      gcongr with i; exact hu i
    refine le_trans this (le_of_eq ?_)
    simp only [DD, dsq, ← Finset.mul_sum, Finset.sum_add_distrib]; ring
  refine ⟨hsum _ (key (fun i => grad1 (F i)) (fun i => hess12 (f i)) (Calc.grad1F_lip hA)
      hA.hess12_lip (Calc.hess12_norm hA)), hsum _ (fun i => ?_),
    hsum _ (keyq (fun i => grad2 (F i)) (fun i => hess22 (f i)) (Calc.grad2F_lip hA)
      hA.hess22_lip (Calc.hess22_norm hA))⟩
  -- the `y` direction
  show ‖grad2 (f i) ((s (k + 1)).x i) ((s (k + 1)).y i) - grad2 (f i) ((s k).x i) ((s k).y i)‖ ^ 2 ≤ _
  have h := Calc.grad2f_lip hA i ((s (k + 1)).x i) ((s k).x i) ((s (k + 1)).y i) ((s k).y i)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  refine le_trans h2 ?_
  rw [mul_pow, pdist_sq]
  have := sq_nonneg (LF1 + Lf2 * rv σ LF0)
  simp only [Cd]; nlinarith [sq_nonneg ‖(s (k + 1)).x i - (s k).x i‖,
      sq_nonneg ‖(s (k + 1)).y i - (s k).y i‖, sq_nonneg ‖(s (k + 1)).v i - (s k).v i‖,
      sq_nonneg Lf1]

end RunBounds
end DecBilevel.SLDBO.Main

namespace DecBilevel.SLDBO.Main
open DecBilevel.SLDBO Finset InnerProductSpace

lemma avg_lin3 {n : ℕ} (hn : 0 < n) (u v w : Fin n → ℝ) (a b c d : ℝ) :
    (1 / (n : ℝ)) * ∑ i, (a * u i + b * v i + c * w i + d) =
      a * ((1 / (n : ℝ)) * ∑ i, u i) + b * ((1 / (n : ℝ)) * ∑ i, v i) +
        c * ((1 / (n : ℝ)) * ∑ i, w i) + d := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

lemma norm_sub_sq_le2 {d : ℕ} (a b c : E d) : ‖a - c‖ ^ 2 ≤ 2 * ‖a - b‖ ^ 2 + 2 * ‖b - c‖ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le_norm_sub_add_norm_sub a b c) 2
  nlinarith [sq_nonneg (‖a - b‖ - ‖b - c‖)]

lemma avg_eq_smul_sum {n d : ℕ} (z : Fin n → E d) : avg z = (1 / (n : ℝ)) • ∑ i, z i := rfl

section ErrBounds
variable {n p q : ℕ} {W : Matrix (Fin n) (Fin n) ℝ} {F f : Fin n → E p → E q → ℝ}
  {σ LF0 LF1 Lf1 Lf2 ρ α β η : ℝ} {x0 : E p} {y0 v0 : E q} {ystar : E p → E q}
  (hA : Assumption21 F f σ LF0 LF1 Lf1 Lf2) (hn : 0 < n) (hv0 : ‖v0‖ ≤ rv σ LF0)
  (hys : ∀ x, IsMinOn (avgf f x) Set.univ (ystar x))

local notation "𝓢" => run W F f α β η (rv σ LF0) x0 y0 v0

include hA hn hv0

/-- the per-agent square bound `((L₁)P + L_{f,1}‖vᵢ − v̂‖)²` summed, with `v̂` arbitrary. -/
lemma pair_sum_bound (k : ℕ) (yh vh : E q) :
    (1 / (n : ℝ)) * ∑ i, ((LF1 + Lf2 * rv σ LF0) * pdist ((𝓢 k).x i) (avg (𝓢 k).x) ((𝓢 k).y i) yh +
        Lf1 * ‖(𝓢 k).v i - vh‖) ^ 2 ≤
      2 * (LF1 + Lf2 * rv σ LF0) ^ 2 * (cons (𝓢 k).x + 2 * cons (𝓢 k).y + 2 * ‖avg (𝓢 k).y - yh‖ ^ 2) +
        2 * Lf1 ^ 2 * (2 * cons (𝓢 k).v + 2 * ‖avg (𝓢 k).v - vh‖ ^ 2) := by
  set L := LF1 + Lf2 * rv σ LF0
  have hi : ∀ i, (L * pdist ((𝓢 k).x i) (avg (𝓢 k).x) ((𝓢 k).y i) yh + Lf1 * ‖(𝓢 k).v i - vh‖) ^ 2 ≤
      (2 * L ^ 2) * ‖(𝓢 k).x i - avg (𝓢 k).x‖ ^ 2 + (4 * L ^ 2) * ‖(𝓢 k).y i - avg (𝓢 k).y‖ ^ 2 +
        (4 * Lf1 ^ 2) * ‖(𝓢 k).v i - avg (𝓢 k).v‖ ^ 2 +
        (4 * L ^ 2 * ‖avg (𝓢 k).y - yh‖ ^ 2 + 4 * Lf1 ^ 2 * ‖avg (𝓢 k).v - vh‖ ^ 2) := by
    intro i
    refine le_trans Gen.sq_add_le_two ?_
    rw [mul_pow, mul_pow, pdist_sq]
    have h1 := norm_sub_sq_le2 ((𝓢 k).y i) (avg (𝓢 k).y) yh
    have h2 := norm_sub_sq_le2 ((𝓢 k).v i) (avg (𝓢 k).v) vh
    nlinarith [sq_nonneg L, sq_nonneg Lf1, mul_le_mul_of_nonneg_left h1 (sq_nonneg L),
      mul_le_mul_of_nonneg_left h2 (sq_nonneg Lf1)]
  have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have h3 := mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ 1 / (n:ℝ))
  rw [avg_lin3 hn] at h3
  refine le_trans h3 (le_of_eq ?_)
  simp only [cons]; ring

include hys

/-- `‖∇Φ(x̄) − d̄ₓ‖² ≤ 4L₁²(X+Y+e) + 4L_{f,1}²(Z+w)`. -/
lemma hyper_err (k : ℕ) :
    ‖hypergrad F f ystar (avg (𝓢 k).x) - avg (dirX 𝓢 k)‖ ^ 2 ≤
      4 * (LF1 + Lf2 * rv σ LF0) ^ 2 * (cons (𝓢 k).x + cons (𝓢 k).y +
        ‖avg (𝓢 k).y - ystar (avg (𝓢 k).x)‖ ^ 2) +
      4 * Lf1 ^ 2 * (cons (𝓢 k).v + ‖avg (𝓢 k).v - vstar F f ystar (avg (𝓢 k).x)‖ ^ 2) := by
  set xb := avg (𝓢 k).x
  set ys := ystar xb
  set vs := vstar F f ystar xb
  have hr := rv_nonneg hA
  have hvle : ∀ i, ‖(𝓢 k).v i‖ ≤ rv σ LF0 :=
    fun i => Aux.v_norm_le W F f α β η _ x0 y0 v0 hr hv0 k i
  have e1 : hypergrad F f ystar xb =
      (1 / (n : ℝ)) • ∑ i, (grad1 (F i) xb ys - hess12 (f i) xb ys vs) := by
    simp only [hypergrad, avgGrad1, avgHess12, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sum_apply, Finset.sum_sub_distrib, smul_sub]
    rfl
  have e2 : avg (dirX 𝓢 k) = (1 / (n : ℝ)) • ∑ i, (grad1 (F i) ((𝓢 k).x i) ((𝓢 k).y i) -
      hess12 (f i) ((𝓢 k).x i) ((𝓢 k).y i) ((𝓢 k).v i)) := rfl
  rw [norm_sub_rev, e1, e2]
  refine le_trans (avg_err hn (fun i => grad1 (F i)) (fun i => hess12 (f i)) hA.Lf2_nonneg
    (Calc.grad1F_lip hA) hA.hess12_lip (Calc.hess12_norm hA) _ _ _ hvle xb ys vs) ?_
  refine le_trans (pair_sum_bound hA hn hv0 k ys vs) ?_
  have := cons_nonneg (𝓢 k).x; have := cons_nonneg (𝓢 k).y; have := cons_nonneg (𝓢 k).v
  nlinarith [sq_nonneg (LF1 + Lf2 * rv σ LF0), sq_nonneg Lf1,
    sq_nonneg ‖avg (𝓢 k).y - ys‖, sq_nonneg ‖avg (𝓢 k).v - vs‖,
    mul_nonneg (sq_nonneg (LF1 + Lf2 * rv σ LF0)) (cons_nonneg (𝓢 k).x),
    mul_nonneg (sq_nonneg (LF1 + Lf2 * rv σ LF0)) (cons_nonneg (𝓢 k).y),
    mul_nonneg (sq_nonneg Lf1) (cons_nonneg (𝓢 k).v)]

omit hys in
/-- `‖d̄ᵥ‖² ≤ 4L₁²(X+Y+e) + 4L_{f,1}²(Z+w)`. -/
lemma dv_bound (k : ℕ) :
    ‖avg (dirV 𝓢 k)‖ ^ 2 ≤
      4 * (LF1 + Lf2 * rv σ LF0) ^ 2 * (cons (𝓢 k).x + cons (𝓢 k).y +
        ‖avg (𝓢 k).y - ystar (avg (𝓢 k).x)‖ ^ 2) +
      4 * Lf1 ^ 2 * (cons (𝓢 k).v + ‖avg (𝓢 k).v - vstar F f ystar (avg (𝓢 k).x)‖ ^ 2) := by
  set xb := avg (𝓢 k).x
  set ys := ystar xb
  set vs := vstar F f ystar xb
  have hr := rv_nonneg hA
  have hvle : ∀ i, ‖(𝓢 k).v i‖ ≤ rv σ LF0 :=
    fun i => Aux.v_norm_le W F f α β η _ x0 y0 v0 hr hv0 k i
  have e1 : (0 : E q) = (1 / (n : ℝ)) • ∑ i, (grad2 (F i) xb ys - hess22 (f i) xb ys vs) := by
    have := Calc.vstar_eq (F := F) (ystar := ystar) hA hn xb
    simp only [avgHess22, avgGrad2, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sum_apply] at this
    rw [Finset.sum_sub_distrib, smul_sub, ← this, sub_self]
  have e2 : avg (dirV 𝓢 k) = (1 / (n : ℝ)) • ∑ i, (grad2 (F i) ((𝓢 k).x i) ((𝓢 k).y i) -
      hess22 (f i) ((𝓢 k).x i) ((𝓢 k).y i) ((𝓢 k).v i)) := rfl
  rw [← sub_zero (avg (dirV 𝓢 k)), e1, e2]
  refine le_trans (avg_err hn (fun i => grad2 (F i)) (fun i => hess22 (f i)) hA.Lf2_nonneg
    (Calc.grad2F_lip hA) hA.hess22_lip (Calc.hess22_norm hA) _ _ _ hvle xb ys vs) ?_
  refine le_trans (pair_sum_bound hA hn hv0 k ys vs) ?_
  nlinarith [sq_nonneg (LF1 + Lf2 * rv σ LF0), sq_nonneg Lf1,
    sq_nonneg ‖avg (𝓢 k).y - ys‖, sq_nonneg ‖avg (𝓢 k).v - vs‖,
    mul_nonneg (sq_nonneg (LF1 + Lf2 * rv σ LF0)) (cons_nonneg (𝓢 k).x),
    mul_nonneg (sq_nonneg (LF1 + Lf2 * rv σ LF0)) (cons_nonneg (𝓢 k).y),
    mul_nonneg (sq_nonneg Lf1) (cons_nonneg (𝓢 k).v)]

/-- `‖d̄ᵥ − (∇₂F(x̄,y*) − ∇²₂₂f(x̄,y*) v̄)‖² ≤ 4L₁²(X+Y+e) + 4L_{f,1}² Z`. -/
lemma dv_err (k : ℕ) :
    ‖avg (dirV 𝓢 k) - (avgGrad2 F (avg (𝓢 k).x) (ystar (avg (𝓢 k).x)) -
        avgHess22 f (avg (𝓢 k).x) (ystar (avg (𝓢 k).x)) (avg (𝓢 k).v))‖ ^ 2 ≤
      4 * (LF1 + Lf2 * rv σ LF0) ^ 2 * (cons (𝓢 k).x + cons (𝓢 k).y +
        ‖avg (𝓢 k).y - ystar (avg (𝓢 k).x)‖ ^ 2) + 4 * Lf1 ^ 2 * cons (𝓢 k).v := by
  set xb := avg (𝓢 k).x
  set ys := ystar xb
  set vb := avg (𝓢 k).v
  have hr := rv_nonneg hA
  have hvle : ∀ i, ‖(𝓢 k).v i‖ ≤ rv σ LF0 :=
    fun i => Aux.v_norm_le W F f α β η _ x0 y0 v0 hr hv0 k i
  have e1 : avgGrad2 F xb ys - avgHess22 f xb ys vb =
      (1 / (n : ℝ)) • ∑ i, (grad2 (F i) xb ys - hess22 (f i) xb ys vb) := by
    simp only [avgGrad2, avgHess22, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sum_apply, Finset.sum_sub_distrib, smul_sub]
  have e2 : avg (dirV 𝓢 k) = (1 / (n : ℝ)) • ∑ i, (grad2 (F i) ((𝓢 k).x i) ((𝓢 k).y i) -
      hess22 (f i) ((𝓢 k).x i) ((𝓢 k).y i) ((𝓢 k).v i)) := rfl
  rw [e1, e2]
  refine le_trans (avg_err hn (fun i => grad2 (F i)) (fun i => hess22 (f i)) hA.Lf2_nonneg
    (Calc.grad2F_lip hA) hA.hess22_lip (Calc.hess22_norm hA) _ _ _ hvle xb ys vb) ?_
  refine le_trans (pair_sum_bound hA hn hv0 k ys vb) ?_
  rw [sub_self, norm_zero]
  nlinarith [sq_nonneg (LF1 + Lf2 * rv σ LF0), sq_nonneg Lf1,
    sq_nonneg ‖avg (𝓢 k).y - ys‖,
    mul_nonneg (sq_nonneg (LF1 + Lf2 * rv σ LF0)) (cons_nonneg (𝓢 k).x),
    mul_nonneg (sq_nonneg (LF1 + Lf2 * rv σ LF0)) (cons_nonneg (𝓢 k).y),
    mul_nonneg (sq_nonneg Lf1) (cons_nonneg (𝓢 k).v)]

/-- `‖d̄_y‖² ≤ 2L_{f,1}²(X+Y+e)`. -/
lemma dy_bound (k : ℕ) :
    ‖avg (dirY 𝓢 k)‖ ^ 2 ≤ 2 * Lf1 ^ 2 * (cons (𝓢 k).x + cons (𝓢 k).y +
        ‖avg (𝓢 k).y - ystar (avg (𝓢 k).x)‖ ^ 2) := by
  set xb := avg (𝓢 k).x
  set ys := ystar xb
  have hr := rv_nonneg hA
  have hvle : ∀ i, ‖(𝓢 k).v i‖ ≤ rv σ LF0 :=
    fun i => Aux.v_norm_le W F f α β η _ x0 y0 v0 hr hv0 k i
  have e1 : (0 : E q) = (1 / (n : ℝ)) • ∑ i, (grad2 (f i) xb ys - (0 : E q →L[ℝ] E q) 0) := by
    have := Calc.ystar_stat hA hn hys xb
    simp only [ContinuousLinearMap.zero_apply, sub_zero]; exact this.symm
  have e2 : avg (dirY 𝓢 k) = (1 / (n : ℝ)) • ∑ i, (grad2 (f i) ((𝓢 k).x i) ((𝓢 k).y i) -
      (0 : E q →L[ℝ] E q) ((𝓢 k).v i)) := by
    simp only [ContinuousLinearMap.zero_apply, sub_zero]; rfl
  rw [← sub_zero (avg (dirY 𝓢 k)), e1, e2]
  refine le_trans (avg_err (a := Lf1) (b := 0) (c := 0) hn (fun i => grad2 (f i))
    (fun _ _ _ => (0 : E q →L[ℝ] E q))
    (le_refl (0:ℝ)) (Calc.grad2f_lip hA) (fun _ _ _ _ _ => by simp) (fun _ _ _ => by simp)
    _ _ _ hvle xb ys 0) ?_
  simp only [zero_mul, add_zero]
  have hi : ∀ i, (Lf1 * pdist ((𝓢 k).x i) xb ((𝓢 k).y i) ys) ^ 2 ≤
      Lf1 ^ 2 * ‖(𝓢 k).x i - xb‖ ^ 2 + (2 * Lf1 ^ 2) * ‖(𝓢 k).y i - avg (𝓢 k).y‖ ^ 2 +
        0 * ‖(𝓢 k).v i‖ ^ 2 + 2 * Lf1 ^ 2 * ‖avg (𝓢 k).y - ys‖ ^ 2 := by
    intro i
    rw [mul_pow, pdist_sq]
    have h1 := norm_sub_sq_le2 ((𝓢 k).y i) (avg (𝓢 k).y) ys
    nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg Lf1)]
  have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have h3 := mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ 1 / (n:ℝ))
  rw [avg_lin3 hn] at h3
  refine le_trans h3 ?_
  have hX : (1 / (n:ℝ)) * ∑ i, ‖(𝓢 k).x i - xb‖ ^ 2 = cons (𝓢 k).x := rfl
  have hY : (1 / (n:ℝ)) * ∑ i, ‖(𝓢 k).y i - avg (𝓢 k).y‖ ^ 2 = cons (𝓢 k).y := rfl
  rw [hX, hY, zero_mul, add_zero]
  nlinarith [sq_nonneg Lf1, mul_nonneg (sq_nonneg Lf1) (cons_nonneg (𝓢 k).x),
    mul_nonneg (sq_nonneg Lf1) (cons_nonneg (𝓢 k).y)]

end ErrBounds
end DecBilevel.SLDBO.Main

namespace DecBilevel.SLDBO.A10
open DecBilevel.SLDBO Finset InnerProductSpace

/-- Cauchy–Schwarz for a symmetric positive semidefinite operator. -/
lemma psd_cs {d : ℕ} (A : E d →L[ℝ] E d) (hsym : ∀ u w, inner ℝ (A u) w = inner ℝ u (A w))
    (hpsd : ∀ u, 0 ≤ inner ℝ (A u) u) (u w : E d) :
    inner ℝ (A u) w ^ 2 ≤ inner ℝ (A u) u * inner ℝ (A w) w := by
  set a := inner ℝ (A u) u
  set b := inner ℝ (A u) w
  set c := inner ℝ (A w) w
  have quad : ∀ t : ℝ, 0 ≤ a + 2 * t * b + t ^ 2 * c := by
    intro t
    have h := hpsd (u + t • w)
    have e : inner ℝ (A (u + t • w)) (u + t • w) = a + 2 * t * b + t ^ 2 * c := by
      simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right]
      have : inner ℝ (A w) u = b := by rw [hsym, real_inner_comm]
      rw [this]; ring
    rwa [e] at h
  have ha : 0 ≤ a := hpsd u
  have hc : 0 ≤ c := hpsd w
  rcases hc.eq_or_lt with h0 | hpos
  · -- c = 0 forces b = 0
    rw [← h0, mul_zero]
    by_contra hb
    push Not at hb
    have hb0 : b ≠ 0 := by intro h; rw [h] at hb; simp at hb
    have := quad (-(a + 1) / (2 * b))
    rw [← h0] at this
    have e : a + 2 * (-(a + 1) / (2 * b)) * b + (-(a + 1) / (2 * b)) ^ 2 * 0 = -1 := by
      field_simp; ring
    linarith
  · have := quad (-b / c)
    have e : a + 2 * (-b / c) * b + (-b / c) ^ 2 * c = a - b ^ 2 / c := by
      field_simp; ring
    rw [e] at this
    have : b ^ 2 / c ≤ a := by linarith
    rw [div_le_iff₀ hpos] at this
    linarith

/-- `‖(I − ηH)u‖ ≤ (1 − ησ)‖u‖` for a symmetric `H` with `σ ≤ H`, `‖H‖ ≤ L`, `η(L+σ) ≤ 2`. -/
lemma contract_op {d : ℕ} (H : E d →L[ℝ] E d) {σ L η : ℝ}
    (hsym : ∀ u w, inner ℝ (H u) w = inner ℝ u (H w))
    (hcoer : ∀ u, σ * ‖u‖ ^ 2 ≤ inner ℝ (H u) u) (hnorm : ‖H‖ ≤ L)
    (hη : 0 < η) (hη2 : η * (L + σ) ≤ 2) (hησ : η * σ ≤ 1) (u : E d) :
    ‖u - η • H u‖ ^ 2 ≤ (1 - η * σ) ^ 2 * ‖u‖ ^ 2 := by
  set A : E d →L[ℝ] E d := H - σ • ContinuousLinearMap.id ℝ (E d)
  have hA : ∀ w, A w = H w - σ • w := fun w => rfl
  have hAsym : ∀ u w, inner ℝ (A u) w = inner ℝ u (A w) := by
    intro u w; rw [hA, hA, inner_sub_left, inner_sub_right, hsym, real_inner_smul_left,
      real_inner_smul_right]
  have hApsd : ∀ w, 0 ≤ inner ℝ (A w) w := by
    intro w; rw [hA, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    linarith [hcoer w]
  have hAup : ∀ w, inner ℝ (A w) w ≤ (L - σ) * ‖w‖ ^ 2 := by
    intro w; rw [hA, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have h1 := real_inner_le_norm (H w) w
    have h2 : ‖H w‖ ≤ L * ‖w‖ := le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
    have := mul_le_mul_of_nonneg_right h2 (norm_nonneg w)
    nlinarith
  have key : ‖A u‖ ^ 2 ≤ (L - σ) * inner ℝ (A u) u := by
    have hcs := psd_cs A hAsym hApsd u (A u)
    rw [real_inner_self_eq_norm_sq] at hcs
    have h2 := hAup (A u)
    rcases (norm_nonneg (A u)).eq_or_lt with h0 | hpos
    · have hz : A u = 0 := norm_eq_zero.mp h0.symm
      rw [hz, norm_zero]; simp
    · have hp : 0 < ‖A u‖ ^ 2 := by positivity
      have : (‖A u‖ ^ 2) * ‖A u‖ ^ 2 ≤ ((L - σ) * inner ℝ (A u) u) * ‖A u‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_left h2 (hApsd u)
        nlinarith
      exact le_of_mul_le_mul_right this hp
  have e : u - η • H u = (1 - η * σ) • u - η • A u := by
    rw [hA, smul_sub, sub_smul, one_smul, smul_smul]; abel
  rw [e, norm_sub_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - η * σ), abs_of_pos hη, real_inner_smul_left,
    real_inner_smul_right, real_inner_comm]
  have hp := hApsd u
  have h3 : η ^ 2 * ‖A u‖ ^ 2 ≤ η ^ 2 * ((L - σ) * inner ℝ (A u) u) :=
    mul_le_mul_of_nonneg_left key (sq_nonneg η)
  have h4 : η ^ 2 * (L - σ) ≤ 2 * η * (1 - η * σ) := by nlinarith
  have h5 := mul_le_mul_of_nonneg_right h4 hp
  nlinarith

end DecBilevel.SLDBO.A10

namespace DecBilevel.SLDBO.Main
lemma norm_add_sq_le_sq_add_aux {d : ℕ} (a b : E d) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 :=
  le_trans (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2) Gen.sq_add_le_two
end DecBilevel.SLDBO.Main

namespace DecBilevel.SLDBO.A10
open DecBilevel.SLDBO Finset InnerProductSpace

section
variable {n p q : ℕ} {W : Matrix (Fin n) (Fin n) ℝ} {F f : Fin n → E p → E q → ℝ}
  {σ LF0 LF1 Lf1 Lf2 ρ α β η : ℝ} {x0 : E p} {y0 v0 : E q} {ystar : E p → E q}
  (hA : Assumption21 F f σ LF0 LF1 Lf1 Lf2) (hW : Assumption22 W ρ) (hn : 0 < n)
  (hv0 : ‖v0‖ ≤ rv σ LF0) (hys : ∀ x, IsMinOn (avgf f x) Set.univ (ystar x))

local notation "𝓢" => run W F f α β η (rv σ LF0) x0 y0 v0

include hA hW hn hv0 hys

/-- Lemma A.10 under `η L_{f,1} < 1` (normalized form). -/
theorem lemmaA10 (k : ℕ) (hη : 0 < η) (hηL : η * Lf1 < 1) :
    ‖avg (𝓢 (k + 1)).v - vstar F f ystar (avg (𝓢 k).x)‖ ^ 2 ≤
      (1 - η * σ / 2) * ‖avg (𝓢 k).v - vstar F f ystar (avg (𝓢 k).x)‖ ^ 2 +
      3 * η * (LF1 + Lf2 * rv σ LF0) ^ 2 / σ * ‖avg (𝓢 k).y - ystar (avg (𝓢 k).x)‖ ^ 2 +
      9 * η * (LF1 + Lf2 * rv σ LF0) ^ 2 / σ * (Main.cons (𝓢 k).x + Main.cons (𝓢 k).y) +
      2 * η ^ 2 * ρ ^ 2 * Main.cons (trV 𝓢 k) +
      (9 * η * Lf1 ^ 2 / σ + 2 * ρ ^ 2) * Main.cons (𝓢 k).v := by
  have hσ := hA.sigma_pos
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hr := Main.rv_nonneg hA
  have hL1 := Main.L1_nonneg hA
  have hX := Main.cons_nonneg (𝓢 k).x
  have hY := Main.cons_nonneg (𝓢 k).y
  have hZ := Main.cons_nonneg (𝓢 k).v
  have hR := Main.cons_nonneg (trV 𝓢 k)
  set xb := avg (𝓢 k).x
  set yb := avg (𝓢 k).y
  set ys := ystar xb
  set vs := vstar F f ystar xb
  set vb := avg (𝓢 k).v
  set t := trV 𝓢 k
  set L := LF1 + Lf2 * rv σ LF0
  -- degenerate case
  by_cases hησ : η * σ ≤ 1
  swap
  · push Not at hησ
    have htriv : ∀ u : E q, u = 0 := by
      intro u
      have h1 := Calc.avgGrad2f_mono hA hn xb (yb + u) yb
      have h2 := Calc.avgGrad2f_lip hA hn xb xb (yb + u) yb
      rw [Calc.pdist_same_x, add_sub_cancel_left] at h2
      rw [add_sub_cancel_left] at h1
      have h3 := real_inner_le_norm (avgGrad2 f xb (yb + u) - avgGrad2 f xb yb) u
      have h4 : σ * ‖u‖ ^ 2 ≤ Lf1 * ‖u‖ ^ 2 := by nlinarith [norm_nonneg u]
      have hσL : Lf1 < σ := by
        by_contra hc; push Not at hc
        have := mul_le_mul_of_nonneg_left hc hη.le
        linarith
      have : ‖u‖ ^ 2 ≤ 0 := by nlinarith
      have : ‖u‖ = 0 := by nlinarith [norm_nonneg u]
      exact norm_eq_zero.mp this
    rw [htriv (avg (𝓢 (k + 1)).v - vs), htriv (vb - vs), htriv (yb - ys), norm_zero]
    have : 0 ≤ 9 * η * L ^ 2 / σ * (Main.cons (𝓢 k).x + Main.cons (𝓢 k).y) := by positivity
    have : 0 ≤ 2 * η ^ 2 * ρ ^ 2 * Main.cons t := by positivity
    have : 0 ≤ (9 * η * Lf1 ^ 2 / σ + 2 * ρ ^ 2) * Main.cons (𝓢 k).v := by positivity
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add]
    linarith
  set z : Fin n → E q := fun i => ∑ j, W i j • ((𝓢 k).v j + η • t j)
  have hv' : (𝓢 (k + 1)).v = fun i => ballProj (rv σ LF0) (z i) :=
    Aux.v_succ W F f α β η _ x0 y0 v0 k
  have hvs : ‖vs‖ ≤ rv σ LF0 := Calc.vstar_norm hA hn hys xb
  have h12 : ‖avg (𝓢 (k + 1)).v - vs‖ ^ 2 ≤ (1 / (n : ℝ)) * ∑ i, ‖z i - vs‖ ^ 2 := by
    refine le_trans (Gen.norm_avg_sub_sq_le hn _ vs) ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum; intro i _
    rw [hv']
    apply pow_le_pow_left₀ (norm_nonneg _)
    conv_lhs => rw [← Aux.ballProj_of_le hvs]
    exact Aux.ballProj_nonexp hr _ _
  have h3 : (1 / (n : ℝ)) * ∑ i, ‖z i - vs‖ ^ 2 =
      (1 / (n : ℝ)) * ∑ i, ‖z i - avg z‖ ^ 2 + ‖avg z - vs‖ ^ 2 := by
    rw [Gen.sum_sq_sub_eq z vs, mul_add]; field_simp
  have hz : avg z = vb + η • avg t := by
    show avg (fun i => ∑ j, W i j • ((𝓢 k).v j + η • t j)) = _
    rw [Aux.avg_mix hW, Aux.avg_add, Aux.avg_smul]
  -- consensus part of z
  have h4 : (1 / (n : ℝ)) * ∑ i, ‖z i - avg z‖ ^ 2 ≤ 2 * ρ ^ 2 * Main.cons (𝓢 k).v +
      2 * η ^ 2 * ρ ^ 2 * Main.cons t := by
    have e : ∀ i, z i - avg z = (∑ j, W i j • ((𝓢 k).v j - vb)) + η • (∑ j, W i j • (t j - avg t)) := by
      intro i
      rw [hz, ← Aux.mix_sub_avg hW, ← Aux.mix_sub_avg hW]
      simp only [z, smul_add, Finset.sum_add_distrib, smul_sub]
      rw [Finset.smul_sum]
      simp only [smul_comm η (W i _)]
      abel
    have hb1 := (Aux.lemmaA1 W ρ hW (𝓢 k).v).2
    have hb2 := (Aux.lemmaA1 W ρ hW t).2
    have hi : ∀ i, ‖z i - avg z‖ ^ 2 ≤ 2 * ‖∑ j, W i j • ((𝓢 k).v j - vb)‖ ^ 2 +
        2 * η ^ 2 * ‖∑ j, W i j • (t j - avg t)‖ ^ 2 := by
      intro i
      rw [e i]
      refine le_trans (Main.norm_add_sq_le_sq_add_aux _ _) ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη, mul_pow]; ring_nf; rfl
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at this
    have h5 : (1 / (n:ℝ)) * ∑ i, ‖z i - avg z‖ ^ 2 ≤ (1 / (n:ℝ)) *
        (2 * (ρ ^ 2 * ∑ i, ‖(𝓢 k).v i - vb‖ ^ 2) + 2 * η ^ 2 * (ρ ^ 2 * ∑ i, ‖t i - avg t‖ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      refine le_trans this ?_
      have := mul_le_mul_of_nonneg_left hb1 (by norm_num : (0:ℝ) ≤ 2)
      have := mul_le_mul_of_nonneg_left hb2 (by positivity : (0:ℝ) ≤ 2 * η ^ 2)
      linarith
    refine le_trans h5 (le_of_eq ?_)
    simp only [Main.cons]; ring
  -- the mean part
  have hdv : avg t = avg (dirV 𝓢 k) := (Aux.eq25 F f α β η (rv σ LF0) x0 y0 v0 hW k).2.2.2.2
  set Hb := avgHess22 f xb yb
  set gb := avgGrad2 F xb yb
  set Hs := avgHess22 f xb ys
  set gs := avgGrad2 F xb ys
  have hHv : Hs vs = gs := Calc.vstar_eq (F := F) (ystar := ystar) hA hn xb
  set u1 := (vb - vs) - η • Hb (vb - vs)
  set cc := (gb - gs) - (Hb - Hs) vs
  set b := η • (avg (dirV 𝓢 k) - (gb - Hb vb))
  have hsplit : avg z - vs = (u1 + η • cc) + b := by
    rw [hz, hdv]
    simp only [u1, cc, b, map_sub, ContinuousLinearMap.sub_apply, hHv, smul_sub]
    abel
  have hcc : ‖cc‖ ≤ L * ‖yb - ys‖ := by
    have h := Gen.pair_bound gs gb Hs Hb vs vs (Calc.avgGrad2F_lip hA hn xb xb yb ys)
      (Calc.avgHess22_lip hA hn xb xb yb ys) (le_refl _) hvs (Calc.pdist_nonneg _ _ _ _)
      hA.Lf2_nonneg
    rw [Calc.pdist_same_x, sub_self, norm_zero, mul_zero, add_zero] at h
    have e : (gb - Hb vs) - (gs - Hs vs) = cc := by
      simp only [cc, ContinuousLinearMap.sub_apply]; abel
    rw [e] at h; exact h
  have hu1 : ‖u1‖ ^ 2 ≤ (1 - η * σ) ^ 2 * ‖vb - vs‖ ^ 2 := by
    apply contract_op Hb (L := Lf1) (fun u w => Calc.avgHess22_symm hA hn xb yb u w)
      (Calc.avgHess22_coercive hA hn xb yb) (Calc.avgHess22_norm hA hn xb yb) hη _ hησ
    nlinarith
  set w := ‖vb - vs‖ ^ 2
  set e := ‖yb - ys‖ ^ 2
  have hw : 0 ≤ w := sq_nonneg _
  have he : 0 ≤ e := sq_nonneg _
  have hLe : 0 ≤ L ^ 2 * e := mul_nonneg (sq_nonneg L) he
  have hησ0 : 0 < η * σ := mul_pos hη hσ
  have hησ1 : 0 ≤ 1 - η * σ := by linarith
  have hΔ5 : ‖u1 + η • cc‖ ^ 2 ≤ (1 - η * σ) * w + 2 * η / σ * (L ^ 2 * e) := by
    refine le_trans (Gen.norm_add_sq_young u1 (η • cc) hησ0) ?_
    have hc2 : ‖η • cc‖ ^ 2 ≤ η ^ 2 * (L ^ 2 * e) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη, mul_pow]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg η)
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hcc 2
    have q1 : (1 + η * σ) * ‖u1‖ ^ 2 ≤ (1 - η * σ) * w := by
      have t1 := mul_le_mul_of_nonneg_left hu1 (by linarith : (0:ℝ) ≤ 1 + η * σ)
      have t2 : (1 + η * σ) * ((1 - η * σ) ^ 2 * w) = (1 - η * σ) * w - (η * σ) ^ 2 * ((1 - η * σ) * w) := by
        ring
      have t3 := mul_nonneg (sq_nonneg (η * σ)) (mul_nonneg hησ1 hw)
      linarith only [t1, t2, t3]
    have q2 : (1 + 1 / (η * σ)) * ‖η • cc‖ ^ 2 ≤ 2 * η / σ * (L ^ 2 * e) := by
      have hk : (1 + 1 / (η * σ)) * η ^ 2 ≤ 2 * η / σ := by
        have e1 : (1 + 1 / (η * σ)) * η ^ 2 = η ^ 2 + η / σ := by field_simp
        rw [e1]
        have : η ^ 2 ≤ η / σ := by
          rw [le_div_iff₀ hσ]
          have := mul_le_mul_of_nonneg_left hησ hη.le
          linarith only [this]
        have e2 : 2 * η / σ = η / σ + η / σ := by ring
        linarith only [this, e2]
      have hpos : (0:ℝ) ≤ 1 + 1 / (η * σ) := by
        have := one_div_pos.mpr hησ0; linarith
      calc (1 + 1 / (η * σ)) * ‖η • cc‖ ^ 2 ≤ (1 + 1 / (η * σ)) * (η ^ 2 * (L ^ 2 * e)) :=
            mul_le_mul_of_nonneg_left hc2 hpos
        _ = ((1 + 1 / (η * σ)) * η ^ 2) * (L ^ 2 * e) := by ring
        _ ≤ 2 * η / σ * (L ^ 2 * e) := mul_le_mul_of_nonneg_right hk hLe
    linarith only [q1, q2]
  have hb : ‖b‖ ^ 2 ≤ η ^ 2 * (2 * L ^ 2 * (Main.cons (𝓢 k).x + Main.cons (𝓢 k).y) +
      2 * Lf1 ^ 2 * Main.cons (𝓢 k).v) := by
    have hvle : ∀ i, ‖(𝓢 k).v i‖ ≤ rv σ LF0 :=
      fun i => Aux.v_norm_le W F f α β η _ x0 y0 v0 hr hv0 k i
    have e1 : gb - Hb vb = (1 / (n : ℝ)) • ∑ i, (grad2 (F i) xb yb - hess22 (f i) xb yb vb) := by
      simp only [gb, Hb, avgGrad2, avgHess22, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.sum_apply, Finset.sum_sub_distrib, smul_sub]
    have e2 : avg (dirV 𝓢 k) = (1 / (n : ℝ)) • ∑ i, (grad2 (F i) ((𝓢 k).x i) ((𝓢 k).y i) -
        hess22 (f i) ((𝓢 k).x i) ((𝓢 k).y i) ((𝓢 k).v i)) := rfl
    have h1 := Main.avg_err hn (fun i => grad2 (F i)) (fun i => hess22 (f i)) hA.Lf2_nonneg
      (Calc.grad2F_lip hA) hA.hess22_lip (Calc.hess22_norm hA) (𝓢 k).x (𝓢 k).y (𝓢 k).v hvle xb yb vb
    rw [← e1, ← e2] at h1
    have hi : ∀ i, (L * pdist ((𝓢 k).x i) xb ((𝓢 k).y i) yb + Lf1 * ‖(𝓢 k).v i - vb‖) ^ 2 ≤
        (2 * L ^ 2) * ‖(𝓢 k).x i - xb‖ ^ 2 + (2 * L ^ 2) * ‖(𝓢 k).y i - yb‖ ^ 2 +
          (2 * Lf1 ^ 2) * ‖(𝓢 k).v i - vb‖ ^ 2 + 0 := by
      intro i
      refine le_trans Gen.sq_add_le_two ?_
      rw [mul_pow, mul_pow, Main.pdist_sq]; ring_nf; rfl
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
    have h3 := mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ 1 / (n:ℝ))
    rw [Main.avg_lin3 hn] at h3
    have h4 : ‖avg (dirV 𝓢 k) - (gb - Hb vb)‖ ^ 2 ≤
        2 * L ^ 2 * (Main.cons (𝓢 k).x + Main.cons (𝓢 k).y) + 2 * Lf1 ^ 2 * Main.cons (𝓢 k).v := by
      refine le_trans h1 (le_trans h3 (le_of_eq ?_))
      simp only [Main.cons]; ring
    simp only [b]; rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη, mul_pow]
    exact mul_le_mul_of_nonneg_left h4 (sq_nonneg η)
  set Er := 2 * L ^ 2 * (Main.cons (𝓢 k).x + Main.cons (𝓢 k).y) + 2 * Lf1 ^ 2 * Main.cons (𝓢 k).v
  have hXY0 : 0 ≤ Main.cons (𝓢 k).x + Main.cons (𝓢 k).y := add_nonneg hX hY
  have hEr : 0 ≤ Er := add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg L)) hXY0)
    (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg Lf1)) hZ)
  have hηs : 0 ≤ η / σ := div_nonneg hη.le hσ.le
  have h6 : ‖avg z - vs‖ ^ 2 ≤ (1 - η * σ / 2) * w + 3 * η / σ * (L ^ 2 * e) + 3 * η / σ * Er := by
    rw [hsplit]
    have hξ : 0 < η * σ / 2 := half_pos hησ0
    refine le_trans (Gen.norm_add_sq_young _ b hξ) ?_
    have q1 : (1 + η * σ / 2) * ‖u1 + η • cc‖ ^ 2 ≤ (1 - η * σ / 2) * w + 3 * η / σ * (L ^ 2 * e) := by
      have t1 := mul_le_mul_of_nonneg_left hΔ5 (by linarith : (0:ℝ) ≤ 1 + η * σ / 2)
      have t2 : (1 + η * σ / 2) * ((1 - η * σ) * w) ≤ (1 - η * σ / 2) * w := by
        have e0 : (1 + η * σ / 2) * ((1 - η * σ) * w) = (1 - η * σ / 2) * w - (η * σ) ^ 2 / 2 * w := by
          ring
        have := mul_nonneg (sq_nonneg (η * σ)) hw
        linarith only [e0, this]
      have t3 : (1 + η * σ / 2) * (2 * η / σ * (L ^ 2 * e)) ≤ 3 * η / σ * (L ^ 2 * e) := by
        have : 0 ≤ η / σ * (L ^ 2 * e) := mul_nonneg hηs hLe
        have e1 : (1 + η * σ / 2) * (2 * η / σ * (L ^ 2 * e)) =
            2 * (η / σ * (L ^ 2 * e)) + η * σ * (η / σ * (L ^ 2 * e)) := by ring
        have e2 : 3 * η / σ * (L ^ 2 * e) = 3 * (η / σ * (L ^ 2 * e)) := by ring
        have h' : η * σ * (η / σ * (L ^ 2 * e)) ≤ 1 * (η / σ * (L ^ 2 * e)) :=
          mul_le_mul_of_nonneg_right hησ this
        linarith only [e1, e2, h', this]
      calc (1 + η * σ / 2) * ‖u1 + η • cc‖ ^ 2 ≤ (1 + η * σ / 2) * ((1 - η * σ) * w +
            2 * η / σ * (L ^ 2 * e)) := t1
        _ = (1 + η * σ / 2) * ((1 - η * σ) * w) + (1 + η * σ / 2) * (2 * η / σ * (L ^ 2 * e)) := by
            ring
        _ ≤ _ := add_le_add t2 t3
    have q2 : (1 + 1 / (η * σ / 2)) * ‖b‖ ^ 2 ≤ 3 * η / σ * Er := by
      have hk : (1 + 1 / (η * σ / 2)) * η ^ 2 ≤ 3 * η / σ := by
        have e1 : (1 + 1 / (η * σ / 2)) * η ^ 2 = η ^ 2 + 2 * η / σ := by field_simp
        rw [e1]
        have : η ^ 2 ≤ η / σ := by
          rw [le_div_iff₀ hσ]
          have := mul_le_mul_of_nonneg_left hησ hη.le
          linarith only [this]
        have e2 : 3 * η / σ = η / σ + 2 * η / σ := by ring
        linarith only [this, e2]
      have hpos : (0:ℝ) ≤ 1 + 1 / (η * σ / 2) := by
        have := one_div_pos.mpr hξ; linarith
      calc (1 + 1 / (η * σ / 2)) * ‖b‖ ^ 2 ≤ (1 + 1 / (η * σ / 2)) * (η ^ 2 * Er) :=
            mul_le_mul_of_nonneg_left hb hpos
        _ = ((1 + 1 / (η * σ / 2)) * η ^ 2) * Er := by ring
        _ ≤ 3 * η / σ * Er := mul_le_mul_of_nonneg_right hk hEr
    linarith only [q1, q2]
  -- assemble
  have hfin : ‖avg (𝓢 (k + 1)).v - vs‖ ^ 2 ≤ 2 * ρ ^ 2 * Main.cons (𝓢 k).v +
      2 * η ^ 2 * ρ ^ 2 * Main.cons t + ((1 - η * σ / 2) * w + 3 * η / σ * (L ^ 2 * e) +
        3 * η / σ * Er) := by
    rw [h3] at h12; linarith
  refine le_trans hfin ?_
  have k1 : 3 * η / σ * Er ≤ 9 * η * L ^ 2 / σ * (Main.cons (𝓢 k).x + Main.cons (𝓢 k).y) +
      9 * η * Lf1 ^ 2 / σ * Main.cons (𝓢 k).v := by
    have a1 : 0 ≤ η / σ * (L ^ 2 * (Main.cons (𝓢 k).x + Main.cons (𝓢 k).y)) :=
      mul_nonneg hηs (mul_nonneg (sq_nonneg L) hXY0)
    have a2 : 0 ≤ η / σ * (Lf1 ^ 2 * Main.cons (𝓢 k).v) := mul_nonneg hηs (mul_nonneg (sq_nonneg Lf1) hZ)
    have e1 : 3 * η / σ * Er = 6 * (η / σ * (L ^ 2 * (Main.cons (𝓢 k).x + Main.cons (𝓢 k).y))) +
        6 * (η / σ * (Lf1 ^ 2 * Main.cons (𝓢 k).v)) := by simp only [Er]; ring
    have e2 : 9 * η * L ^ 2 / σ * (Main.cons (𝓢 k).x + Main.cons (𝓢 k).y) +
        9 * η * Lf1 ^ 2 / σ * Main.cons (𝓢 k).v =
        9 * (η / σ * (L ^ 2 * (Main.cons (𝓢 k).x + Main.cons (𝓢 k).y))) +
        9 * (η / σ * (Lf1 ^ 2 * Main.cons (𝓢 k).v)) := by ring
    linarith only [e1, e2, a1, a2]
  have e3 : 3 * η / σ * (L ^ 2 * e) = 3 * η * L ^ 2 / σ * e := by ring
  have e4 : (9 * η * Lf1 ^ 2 / σ + 2 * ρ ^ 2) * Main.cons (𝓢 k).v =
      9 * η * Lf1 ^ 2 / σ * Main.cons (𝓢 k).v + 2 * ρ ^ 2 * Main.cons (𝓢 k).v := by ring
  linarith only [k1, e3, e4]

end
end DecBilevel.SLDBO.A10

open DecBilevel.SLDBO

set_option linter.unusedVariables false in
theorem solution {n p q : ℕ} (hn : 0 < n) (W : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ)
    (F f : Fin n → E p → E q → ℝ) (σ LF0 LF1 Lf1 Lf2 : ℝ) (α β η : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hη : 0 < η) (x0 : E p) (y0 v0 : E q)
    (hA21 : Assumption21 F f σ LF0 LF1 Lf1 Lf2) (hA22 : Assumption22 W ρ)
    (hv0 : ‖v0‖ ≤ rv σ LF0)
    (ystar : E p → E q) (hystar : ∀ x, IsMinOn (avgf f x) Set.univ (ystar x)) (hηL : η * Lf1 < 1) (k : ℕ) :
    let s := run W F f α β η (rv σ LF0) x0 y0 v0
    ‖avg (s (k + 1)).v - vstar F f ystar (avg (s k).x)‖ ^ 2 ≤
      (1 - η * σ / 2) * ‖avg (s k).v - vstar F f ystar (avg (s k).x)‖ ^ 2 +
      3 * η * (LF1 + Lf2 * rv σ LF0) ^ 2 / σ * ‖avg (s k).y - ystar (avg (s k).x)‖ ^ 2 +
      9 * η * (LF1 + Lf2 * rv σ LF0) ^ 2 / (n * σ) * ∑ i, (‖(s k).x i - avg (s k).x‖ ^ 2 + ‖(s k).y i - avg (s k).y‖ ^ 2) +
      2 * η ^ 2 * ρ ^ 2 / n * ∑ i, ‖trV s k i - avg (trV s k)‖ ^ 2 +
      (9 * η * Lf1 ^ 2 / σ + 2 * ρ ^ 2) * (1 / n) * ∑ i, ‖(s k).v i - avg (s k).v‖ ^ 2 := by
  intro s
  have h := A10.lemmaA10 (W := W) (α := α) (β := β) (η := η) (x0 := x0) (y0 := y0) (v0 := v0)
    hA21 hA22 hn hv0 hystar k hη hηL
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hσ := hA21.sigma_pos
  have e1 : 9 * η * (LF1 + Lf2 * rv σ LF0) ^ 2 / (n * σ) *
      ∑ i, (‖(s k).x i - avg (s k).x‖ ^ 2 + ‖(s k).y i - avg (s k).y‖ ^ 2) =
      9 * η * (LF1 + Lf2 * rv σ LF0) ^ 2 / σ * (Main.cons (s k).x + Main.cons (s k).y) := by
    simp only [Main.cons, Finset.sum_add_distrib]
    field_simp
  have e2 : 2 * η ^ 2 * ρ ^ 2 / n * ∑ i, ‖trV s k i - avg (trV s k)‖ ^ 2 =
      2 * η ^ 2 * ρ ^ 2 * Main.cons (trV s k) := by
    simp only [Main.cons]; field_simp
  have e3 : (9 * η * Lf1 ^ 2 / σ + 2 * ρ ^ 2) * (1 / n) * ∑ i, ‖(s k).v i - avg (s k).v‖ ^ 2 =
      (9 * η * Lf1 ^ 2 / σ + 2 * ρ ^ 2) * Main.cons (s k).v := by
    simp only [Main.cons]; ring
  rw [e1, e2, e3]; exact h


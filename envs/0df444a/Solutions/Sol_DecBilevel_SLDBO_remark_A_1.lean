-- Prove2me | solution 1 for DecBilevel.SLDBO.remark_A_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T01:09:20.830984+00:00
-- url     : https://prove2.me/submissions/490980ca-68fa-4e03-b00a-e5296ab63bc6

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

open DecBilevel.SLDBO

set_option linter.unusedVariables false in
theorem solution {n p q : ℕ} (hn : 0 < n) (W : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ)
    (F f : Fin n → E p → E q → ℝ) (σ LF0 LF1 Lf1 Lf2 : ℝ) (α β η : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hη : 0 < η) (x0 : E p) (y0 v0 : E q)
    (hA21 : Assumption21 F f σ LF0 LF1 Lf1 Lf2) (hA22 : Assumption22 W ρ)
    (hv0 : ‖v0‖ ≤ rv σ LF0) (k : ℕ) :
    let s := run W F f α β η (rv σ LF0) x0 y0 v0
    (∑ i, ‖(s (k + 1)).x i - avg (s (k + 1)).x‖ ^ 2 ≤
      ρ * ∑ i, ‖(s k).x i - avg (s k).x‖ ^ 2 +
      ρ ^ 2 * α ^ 2 / (1 - ρ) * ∑ i, ‖trX s k i - avg (trX s k)‖ ^ 2) ∧
    (∑ i, ‖(s (k + 1)).y i - avg (s (k + 1)).y‖ ^ 2 ≤
      ρ * ∑ i, ‖(s k).y i - avg (s k).y‖ ^ 2 +
      ρ ^ 2 * β ^ 2 / (1 - ρ) * ∑ i, ‖trY s k i - avg (trY s k)‖ ^ 2) :=
  Aux.remarkA1 F f α β η (rv σ LF0) x0 y0 v0 hA22 k

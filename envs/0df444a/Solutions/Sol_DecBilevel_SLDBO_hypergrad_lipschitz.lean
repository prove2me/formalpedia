-- Prove2me | solution 1 for DecBilevel.SLDBO.hypergrad_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T01:19:55.282285+00:00
-- url     : https://prove2.me/submissions/7f8e3315-e4ba-4bb6-89a8-7b3a61f0e74c

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

open DecBilevel.SLDBO

theorem solution {n p q : ℕ} (hn : 0 < n) (F f : Fin n → E p → E q → ℝ)
    (σ LF0 LF1 Lf1 Lf2 : ℝ) (hA21 : Assumption21 F f σ LF0 LF1 Lf1 Lf2)
    (ystar : E p → E q) (hystar : ∀ x, IsMinOn (avgf f x) Set.univ (ystar x)) (x x' : E p) :
    ‖hypergrad F f ystar x - hypergrad F f ystar x'‖ ≤ LPhi σ LF0 LF1 Lf1 Lf2 * ‖x - x'‖ :=
  Calc.hypergrad_lip hA21 hn hystar x x'

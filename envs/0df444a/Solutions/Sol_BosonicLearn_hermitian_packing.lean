-- Prove2me | solution 1 for BosonicLearn.hermitian_packing
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-14T02:18:02.071811+00:00
-- url     : https://prove2.me/submissions/6381f9bf-e9c5-435a-bc3b-cf1dd7bcc250

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_extreme_singular_values_deviation

open scoped Matrix ComplexOrder
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section


/-! ### Extension of a matrix by zero along an injection -/

/-- The `0/1` matrix of a map `e : σ → κ`. -/
private def extM {σ κ : Type*} [DecidableEq κ] (e : σ → κ) : Matrix κ σ ℝ :=
  Matrix.of fun k c => if k = e c then 1 else 0

private lemma extM_transpose_mul {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ]
    [DecidableEq κ] (e : σ → κ) (he : Function.Injective e) :
    (extM e)ᵀ * extM e = 1 := by
  ext c c'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, extM, Matrix.of_apply, Matrix.one_apply]
  by_cases h : c = c'
  · subst h; simp
  · have : e c' ≠ e c := fun h' => h (he h').symm
    simp [h, this]

private lemma extM_transpose_mulVec {σ κ : Type*} [Fintype σ] [Fintype κ]
    [DecidableEq κ] (e : σ → κ) (x : κ → ℝ) :
    (extM e)ᵀ *ᵥ x = x ∘ e := by
  ext c
  simp [Matrix.mulVec, dotProduct, extM]

private lemma sum_comp_sq_le {σ κ : Type*} [Fintype σ] [Fintype κ]
    (e : σ → κ) (he : Function.Injective e) (x : κ → ℝ) :
    (x ∘ e) ⬝ᵥ (x ∘ e) ≤ x ⬝ᵥ x := by
  classical
  simp only [dotProduct, Function.comp_apply]
  rw [← Finset.sum_image (s := Finset.univ) (g := e) (f := fun k => x k * x k)
    (fun a _ b _ h => he h)]
  exact Finset.sum_le_univ_sum_of_nonneg (fun k => mul_self_nonneg _)

private lemma trace_fromBlocks' {ι : Type*} [Fintype ι] (A B C D : Matrix ι ι ℝ) :
    (Matrix.fromBlocks A B C D).trace = A.trace + D.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]

/-- The real symmetric matrix `c • E [[0, A], [Aᵀ, 0]] Eᵀ`. -/
private def XR {ι κ : Type*} [Fintype ι] [DecidableEq κ] (e : ι ⊕ ι → κ) (c : ℝ)
    (A : Matrix ι ι ℝ) : Matrix κ κ ℝ :=
  c • (extM e * Matrix.fromBlocks 0 A Aᵀ 0 * (extM e)ᵀ)

private lemma XR_transpose {ι κ : Type*} [Fintype ι] [DecidableEq κ] (e : ι ⊕ ι → κ) (c : ℝ)
    (A : Matrix ι ι ℝ) : (XR e c A)ᵀ = XR e c A := by
  simp [XR, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.fromBlocks_transpose,
    Matrix.mul_assoc]

private lemma XR_trace {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ⊕ ι → κ) (he : Function.Injective e) (c : ℝ)
    (A : Matrix ι ι ℝ) : (XR e c A).trace = 0 := by
  rw [XR, Matrix.trace_smul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, extM_transpose_mul e he,
    Matrix.one_mul, trace_fromBlocks']
  simp

private lemma XR_sub {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (e : ι ⊕ ι → κ) (c : ℝ)
    (A B : Matrix ι ι ℝ) : XR e c A - XR e c B = XR e c (A - B) := by
  have h : Matrix.fromBlocks 0 (A - B) (A - B)ᵀ 0
      = Matrix.fromBlocks 0 A Aᵀ 0 - Matrix.fromBlocks (0 : Matrix ι ι ℝ) B Bᵀ 0 := by
    ext (i | i) (j | j) <;> simp
  rw [XR, XR, XR, h, Matrix.mul_sub, Matrix.sub_mul, smul_sub]

private lemma XR_sq_trace {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ⊕ ι → κ) (he : Function.Injective e) (c : ℝ)
    (D : Matrix ι ι ℝ) :
    (XR e c D * XR e c D).trace = 2 * c ^ 2 * ∑ i, ∑ j, D i j ^ 2 := by
  have h1 : XR e c D * XR e c D
      = (c ^ 2) • (extM e * (Matrix.fromBlocks 0 D Dᵀ 0 * Matrix.fromBlocks 0 D Dᵀ 0)
          * (extM e)ᵀ) := by
    simp only [XR, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show c * c = c ^ 2 by ring]
    congr 1
    calc extM e * Matrix.fromBlocks 0 D Dᵀ 0 * (extM e)ᵀ
          * (extM e * Matrix.fromBlocks 0 D Dᵀ 0 * (extM e)ᵀ)
        = extM e * Matrix.fromBlocks 0 D Dᵀ 0 * ((extM e)ᵀ * extM e)
          * Matrix.fromBlocks 0 D Dᵀ 0 * (extM e)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [extM_transpose_mul e he, Matrix.mul_one, Matrix.mul_assoc (extM e)]
  rw [h1, Matrix.trace_smul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, extM_transpose_mul e he,
    Matrix.one_mul, Matrix.fromBlocks_multiply, trace_fromBlocks']
  simp only [Matrix.mul_zero, zero_add, add_zero, smul_eq_mul]
  have h2 : (D * Dᵀ).trace = ∑ i, ∑ j, D i j ^ 2 := by
    simp [Matrix.trace, Matrix.mul_apply, pow_two]
  have h3 : (Dᵀ * D).trace = ∑ i, ∑ j, D i j ^ 2 := by
    rw [Matrix.trace_mul_comm, h2]
  rw [h2, h3]; ring


/-! ### Quadratic form bounds -/

open scoped Matrix.Norms.L2Operator in
private lemma two_dot_mulVec_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (u w : ι → ℝ) : 2 * |u ⬝ᵥ A *ᵥ w| ≤ ‖A‖ * (u ⬝ᵥ u + w ⬝ᵥ w) := by
  have h1 : u ⬝ᵥ A *ᵥ w
      = inner ℝ (WithLp.toLp 2 u : EuclideanSpace ℝ ι) (WithLp.toLp 2 (A *ᵥ w)) := by
    rw [EuclideanSpace.inner_toLp_toLp]; simp [dotProduct_comm]
  have h2 : ‖(WithLp.toLp 2 (A *ᵥ w) : EuclideanSpace ℝ ι)‖
      ≤ ‖A‖ * ‖(WithLp.toLp 2 w : EuclideanSpace ℝ ι)‖ :=
    Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 w)
  have hn : ∀ v : ι → ℝ, ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ ^ 2 = v ⬝ᵥ v := by
    intro v
    rw [EuclideanSpace.norm_sq_eq]
    simp [dotProduct, pow_two]
  have h3 : |u ⬝ᵥ A *ᵥ w| ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ ι)‖
      * (‖A‖ * ‖(WithLp.toLp 2 w : EuclideanSpace ℝ ι)‖) := by
    rw [h1]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
  rw [← hn u, ← hn w]
  have hA : 0 ≤ ‖A‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖(WithLp.toLp 2 u : EuclideanSpace ℝ ι)‖
    - ‖(WithLp.toLp 2 w : EuclideanSpace ℝ ι)‖),
    mul_nonneg hA (sq_nonneg (‖(WithLp.toLp 2 u : EuclideanSpace ℝ ι)‖
    - ‖(WithLp.toLp 2 w : EuclideanSpace ℝ ι)‖))]

open scoped Matrix.Norms.L2Operator in
private lemma XR_quad {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ⊕ ι → κ) (he : Function.Injective e) (c : ℝ) (hc : 0 ≤ c)
    (A : Matrix ι ι ℝ) (x : κ → ℝ) :
    |x ⬝ᵥ XR e c A *ᵥ x| ≤ c * ‖A‖ * (x ⬝ᵥ x) := by
  set y : ι ⊕ ι → ℝ := x ∘ e with hy
  have h1 : x ⬝ᵥ XR e c A *ᵥ x = c * (y ⬝ᵥ Matrix.fromBlocks 0 A Aᵀ 0 *ᵥ y) := by
    rw [XR, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      extM_transpose_mulVec]
  have h2 : y ⬝ᵥ Matrix.fromBlocks 0 A Aᵀ 0 *ᵥ y
      = 2 * ((y ∘ Sum.inl) ⬝ᵥ A *ᵥ (y ∘ Sum.inr)) := by
    have h3 : (y ∘ Sum.inr) ⬝ᵥ Aᵀ *ᵥ (y ∘ Sum.inl) = (y ∘ Sum.inl) ⬝ᵥ A *ᵥ (y ∘ Sum.inr) := by
      rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]
    rw [Matrix.fromBlocks_mulVec]
    simp only [Matrix.zero_mulVec, zero_add, add_zero]
    rw [two_mul]
    nth_rewrite 2 [← h3]
    simp [dotProduct, Fintype.sum_sum_type]
  have h4 : y ⬝ᵥ y = (y ∘ Sum.inl) ⬝ᵥ (y ∘ Sum.inl) + (y ∘ Sum.inr) ⬝ᵥ (y ∘ Sum.inr) := by
    simp [dotProduct, Fintype.sum_sum_type]
  have h5 : y ⬝ᵥ y ≤ x ⬝ᵥ x := sum_comp_sq_le e he x
  have h6 := two_dot_mulVec_le A (y ∘ Sum.inl) (y ∘ Sum.inr)
  have hA : 0 ≤ ‖A‖ := norm_nonneg _
  rw [h1, h2, abs_mul, abs_of_nonneg hc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc c * (2 * |(y ∘ Sum.inl) ⬝ᵥ A *ᵥ (y ∘ Sum.inr)|)
      ≤ c * (‖A‖ * (y ⬝ᵥ y)) := by rw [h4]; exact mul_le_mul_of_nonneg_left h6 hc
    _ ≤ c * (‖A‖ * (x ⬝ᵥ x)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 hA) hc
    _ = c * ‖A‖ * (x ⬝ᵥ x) := by ring

/-! ### Complexification -/

/-- Entrywise complexification of a real matrix. -/
private def cx {κ : Type*} (M : Matrix κ κ ℝ) : Matrix κ κ ℂ := M.map Complex.ofRealHom

private lemma cx_sub {κ : Type*} (M N : Matrix κ κ ℝ) : cx M - cx N = cx (M - N) :=
  (Matrix.map_sub _ (map_sub _) M N).symm

private lemma cx_mul {κ : Type*} [Fintype κ] (M N : Matrix κ κ ℝ) : cx M * cx N = cx (M * N) :=
  Matrix.map_mul.symm

private lemma cx_trace {κ : Type*} [Fintype κ] (M : Matrix κ κ ℝ) :
    (cx M).trace = ((M.trace : ℝ) : ℂ) := by
  simp [cx, Matrix.trace]

private lemma cx_isHermitian {κ : Type*} (M : Matrix κ κ ℝ) (hM : Mᵀ = M) :
    (cx M).IsHermitian := by
  ext i j
  have : M j i = M i j := congrFun (congrFun hM i) j
  simp [cx, Matrix.conjTranspose_apply, this]

private lemma cx_form_re {κ : Type*} [Fintype κ] (M : Matrix κ κ ℝ) (v : κ → ℂ) :
    (star v ⬝ᵥ (cx M *ᵥ v)).re
      = (fun i => (v i).re) ⬝ᵥ M *ᵥ (fun i => (v i).re)
        + (fun i => (v i).im) ⬝ᵥ M *ᵥ (fun i => (v i).im) := by
  simp only [dotProduct, Matrix.mulVec, cx, Matrix.map_apply, Pi.star_apply, Complex.re_sum,
    Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

/-- A real symmetric matrix with `|xᵀ M x| ≤ c ‖x‖²` lies between `-c` and `c` in the complex
Loewner order. -/
private lemma psd_of_real_form {κ : Type*} [Fintype κ] [DecidableEq κ] (M : Matrix κ κ ℝ)
    (hM : Mᵀ = M) (c : ℝ) (h : ∀ x : κ → ℝ, |x ⬝ᵥ M *ᵥ x| ≤ c * (x ⬝ᵥ x)) :
    (((c : ℝ) : ℂ) • (1 : Matrix κ κ ℂ) - cx M).PosSemidef ∧
      (((c : ℝ) : ℂ) • (1 : Matrix κ κ ℂ) + cx M).PosSemidef := by
  have hX : (cx M).IsHermitian := cx_isHermitian M hM
  have hnorm : ∀ v : κ → ℂ, ∑ i, ‖v i‖ ^ 2
      = (fun i => (v i).re) ⬝ᵥ (fun i => (v i).re) + (fun i => (v i).im) ⬝ᵥ (fun i => (v i).im) := by
    intro v
    simp only [dotProduct, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
  have key : ∀ v : κ → ℂ, |(star v ⬝ᵥ (cx M *ᵥ v)).re| ≤ c * ∑ i, ‖v i‖ ^ 2 := by
    intro v
    rw [cx_form_re, hnorm, mul_add]
    exact (abs_add_le _ _).trans (add_le_add (h _) (h _))
  have hsq : ∀ v : κ → ℂ, star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    intro v
    simp only [dotProduct, Pi.star_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  have him : ∀ v : κ → ℂ, (star v ⬝ᵥ (cx M *ᵥ v)).im = 0 := fun v =>
    hX.im_star_dotProduct_mulVec_self v
  have hc1 : (((c : ℝ) : ℂ) • (1 : Matrix κ κ ℂ)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp
  constructor
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hc1.sub hX) fun v => ?_
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      hsq, Complex.nonneg_iff]
    have hk := abs_le.mp (key v)
    constructor
    · simp only [Complex.sub_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      linarith [hk.2]
    · rw [Complex.sub_im, him v, smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_im, sub_zero]
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hc1.add hX) fun v => ?_
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      hsq, Complex.nonneg_iff]
    have hk := abs_le.mp (key v)
    constructor
    · simp only [Complex.add_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      linarith [hk.1]
    · rw [Complex.add_im, him v, smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_im, add_zero]


/-! ### Gaussian measure estimates -/

private lemma sqrt_ratio : (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / 2) = 1 / 2 := by
  have h1 : Real.sqrt (2 * Real.pi) = 2 * Real.sqrt (Real.pi / 2) := by
    rw [show 2 * Real.pi = 2 ^ 2 * (Real.pi / 2) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  have h2 : 0 < Real.sqrt (Real.pi / 2) := Real.sqrt_pos.mpr (by positivity)
  rw [h1]
  field_simp

/-- One-dimensional estimate: `E exp(-2 (g - x)²) ≤ 1/2` for a standard Gaussian `g`. -/
private lemma gauss_one_dim (x : ℝ) :
    ∫ g, Real.exp (-2 * (g - x) ^ 2) ∂(gaussianReal 0 1) ≤ 1 / 2 := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have hint : Integrable
      (fun g : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-2 * (g - x) ^ 2)) :=
    ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 2)).comp_sub_right x).const_mul _
  calc ∫ g, gaussianPDFReal 0 1 g • Real.exp (-2 * (g - x) ^ 2)
      ≤ ∫ g, (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-2 * (g - x) ^ 2) := by
        refine integral_mono_of_nonneg (ae_of_all _ fun g => ?_) hint (ae_of_all _ fun g => ?_)
        · exact mul_nonneg (gaussianPDFReal_nonneg _ _ _) (Real.exp_pos _).le
        · simp only [smul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          rw [gaussianPDFReal]
          simp only [NNReal.coe_one, mul_one]
          have : Real.exp (-(g - 0) ^ 2 / 2) ≤ 1 := by
            rw [Real.exp_le_one_iff]
            have := sq_nonneg (g - 0)
            linarith
          calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(g - 0) ^ 2 / 2)
              ≤ (Real.sqrt (2 * Real.pi))⁻¹ * 1 :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = _ := mul_one _
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * ∫ g, Real.exp (-2 * (g - x) ^ 2) := integral_const_mul _ _
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * ∫ g, Real.exp (-2 * g ^ 2) := by
        rw [integral_sub_right_eq_self (fun g => Real.exp (-2 * g ^ 2)) x]
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / 2) := by rw [integral_gaussian]
    _ = 1 / 2 := sqrt_ratio

private lemma half_pow_le (d : ℕ) :
    Real.exp ((d : ℝ) / 4) * (1 / 2 : ℝ) ^ d ≤ Real.exp (-(d : ℝ) / 4) := by
  have h1 : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2)) := by
    have h2 : Real.exp (1 / 2) ≤ 2 := by
      have h3 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
        rw [← Real.exp_nat_mul]; norm_num
      have h4 := Real.exp_one_lt_d9
      nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    rw [Real.exp_neg]
    calc (1 / 2 : ℝ) = 2⁻¹ := by norm_num
      _ ≤ (Real.exp (1 / 2))⁻¹ := inv_anti₀ (Real.exp_pos _) h2
  have h5 : (1 / 2 : ℝ) ^ d ≤ Real.exp (-(d : ℝ) / 2) := by
    calc (1 / 2 : ℝ) ^ d ≤ Real.exp (-(1 / 2)) ^ d := pow_le_pow_left₀ (by norm_num) h1 d
      _ = Real.exp (-(d : ℝ) / 2) := by rw [← Real.exp_nat_mul]; ring_nf
  calc Real.exp ((d : ℝ) / 4) * (1 / 2 : ℝ) ^ d
      ≤ Real.exp ((d : ℝ) / 4) * Real.exp (-(d : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left h5 (Real.exp_pos _).le
    _ = Real.exp (-(d : ℝ) / 4) := by rw [← Real.exp_add]; ring_nf

/-- Small-ball estimate for the Gaussian matrix measure. -/
private lemma small_ball (s : ℕ) (A₀ : Fin s → Fin s → ℝ) :
    (GaussianMatrix.gaussianMatrix s s)
        {A | ∑ i, ∑ j, (A i j - A₀ i j) ^ 2 ≤ ((s * s : ℕ) : ℝ) / 8}
      ≤ ENNReal.ofReal (Real.exp (-((s * s : ℕ) : ℝ) / 4)) := by
  set d : ℕ := s * s with hd
  set γ := GaussianMatrix.gaussianMatrix s s with hγ
  set F : (Fin s → Fin s → ℝ) → ℝ := fun A => Real.exp (-2 * ∑ i, ∑ j, (A i j - A₀ i j) ^ 2)
    with hF
  have hF_eq : F = fun A => ∏ i, ∏ j, Real.exp (-2 * (A i j - A₀ i j) ^ 2) := by
    funext A
    simp only [hF, Finset.mul_sum, Real.exp_sum]
  have hF_nonneg : ∀ A, 0 ≤ F A := fun A => (Real.exp_pos _).le
  have hF_le : ∀ A, F A ≤ 1 := by
    intro A
    simp only [hF]
    rw [Real.exp_le_one_iff]
    have : 0 ≤ ∑ i, ∑ j, (A i j - A₀ i j) ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    linarith
  have hF_cont : Continuous F := by
    simp only [hF]
    fun_prop
  have hF_int : Integrable F γ := by
    refine Integrable.of_bound hF_cont.aestronglyMeasurable 1 (ae_of_all _ fun A => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hF_nonneg A)]
    exact hF_le A
  have hval : ∫ A, F A ∂γ ≤ (1 / 2 : ℝ) ^ d := by
    rw [hF_eq, hγ, GaussianMatrix.gaussianMatrix,
      integral_fintype_prod_eq_prod
        (f := fun (i : Fin s) (a : Fin s → ℝ) => ∏ j, Real.exp (-2 * (a j - A₀ i j) ^ 2))]
    have h1 : ∀ i : Fin s, ∫ a : Fin s → ℝ, ∏ j, Real.exp (-2 * (a j - A₀ i j) ^ 2)
        ∂(Measure.pi fun _ : Fin s => gaussianReal 0 1) ≤ (1 / 2 : ℝ) ^ s := by
      intro i
      rw [integral_fintype_prod_eq_prod
        (f := fun (j : Fin s) (g : ℝ) => Real.exp (-2 * (g - A₀ i j) ^ 2))]
      calc ∏ j : Fin s, ∫ g, Real.exp (-2 * (g - A₀ i j) ^ 2) ∂(gaussianReal 0 1)
          ≤ ∏ _j : Fin s, (1 / 2 : ℝ) :=
            Finset.prod_le_prod (fun j _ => integral_nonneg fun g => (Real.exp_pos _).le)
              (fun j _ => gauss_one_dim _)
        _ = (1 / 2 : ℝ) ^ s := by simp
    calc ∏ i : Fin s, ∫ a : Fin s → ℝ, ∏ j, Real.exp (-2 * (a j - A₀ i j) ^ 2)
          ∂(Measure.pi fun _ : Fin s => gaussianReal 0 1)
        ≤ ∏ _i : Fin s, (1 / 2 : ℝ) ^ s :=
          Finset.prod_le_prod (fun i _ => integral_nonneg fun a =>
            Finset.prod_nonneg fun j _ => (Real.exp_pos _).le) (fun i _ => h1 i)
      _ = (1 / 2 : ℝ) ^ d := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := γ) (ae_of_all _ hF_nonneg) hF_int
    (Real.exp (-(d : ℝ) / 4))
  have hreal : γ.real {A | Real.exp (-(d : ℝ) / 4) ≤ F A} ≤ Real.exp (-(d : ℝ) / 4) := by
    have h2 : Real.exp (-(d : ℝ) / 4) * γ.real {A | Real.exp (-(d : ℝ) / 4) ≤ F A}
        ≤ (1 / 2 : ℝ) ^ d := hmarkov.trans hval
    have h3 : γ.real {A | Real.exp (-(d : ℝ) / 4) ≤ F A}
        = Real.exp ((d : ℝ) / 4) * (Real.exp (-(d : ℝ) / 4)
          * γ.real {A | Real.exp (-(d : ℝ) / 4) ≤ F A}) := by
      rw [← mul_assoc, ← Real.exp_add]
      ring_nf
      simp
    rw [h3]
    exact (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le).trans (half_pow_le d)
  have hsub : {A : Fin s → Fin s → ℝ | ∑ i, ∑ j, (A i j - A₀ i j) ^ 2 ≤ (d : ℝ) / 8}
      ⊆ {A | Real.exp (-(d : ℝ) / 4) ≤ F A} := by
    intro A hA
    have hA' : ∑ i, ∑ j, (A i j - A₀ i j) ^ 2 ≤ (d : ℝ) / 8 := hA
    show Real.exp (-(d : ℝ) / 4) ≤ Real.exp (-2 * ∑ i, ∑ j, (A i j - A₀ i j) ^ 2)
    apply Real.exp_le_exp.mpr
    linarith
  calc γ {A | ∑ i, ∑ j, (A i j - A₀ i j) ^ 2 ≤ (d : ℝ) / 8}
      ≤ γ {A | Real.exp (-(d : ℝ) / 4) ≤ F A} := measure_mono hsub
    _ = ENNReal.ofReal (γ.real {A | Real.exp (-(d : ℝ) / 4) ≤ F A}) := by
        rw [ofReal_measureReal]
    _ ≤ ENNReal.ofReal (Real.exp (-(d : ℝ) / 4)) := ENNReal.ofReal_le_ofReal hreal

/-- The operator-norm ball of radius `4√s` has Gaussian measure at least `1/2`. -/
private lemma good_set (s : ℕ) (hs : 2 ≤ s) :
    (2⁻¹ : ℝ≥0∞) ≤ (GaussianMatrix.gaussianMatrix s s)
      {A | GaussianMatrix.specNorm (Matrix.of A) ≤ 4 * Real.sqrt s} := by
  have h := GaussianMatrix.extreme_singular_values_deviation (N := s) (n := s) (by omega)
    (2 * Real.sqrt s) (by positivity)
  have hnum : ENNReal.ofReal (2 * Real.exp (-(2 * Real.sqrt s) ^ 2 / 2)) ≤ 2⁻¹ := by
    have h1 : (2 * Real.sqrt s) ^ 2 = 4 * s := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg s)]; norm_num
    have h2 : (2 : ℝ) ≤ s := by exact_mod_cast hs
    have h3 : (5 : ℝ) ≤ Real.exp (2 * s) := by
      have := Real.add_one_le_exp (2 * (s : ℝ))
      linarith
    have h4 : Real.exp (-(2 * Real.sqrt s) ^ 2 / 2) = (Real.exp (2 * s))⁻¹ := by
      rw [h1, ← Real.exp_neg]; congr 1; ring
    have h5 : 2 * Real.exp (-(2 * Real.sqrt s) ^ 2 / 2) ≤ 2⁻¹ := by
      rw [h4]
      have : (Real.exp (2 * s))⁻¹ ≤ 5⁻¹ := inv_anti₀ (by norm_num) h3
      linarith
    calc ENNReal.ofReal (2 * Real.exp (-(2 * Real.sqrt s) ^ 2 / 2))
        ≤ ENNReal.ofReal 2⁻¹ := ENNReal.ofReal_le_ofReal h5
      _ = 2⁻¹ := by
          rw [ENNReal.ofReal_inv_of_pos (by norm_num)]; simp
  calc (2⁻¹ : ℝ≥0∞) = 1 - 2⁻¹ := ENNReal.one_sub_inv_two.symm
    _ ≤ 1 - ENNReal.ofReal (2 * Real.exp (-(2 * Real.sqrt s) ^ 2 / 2)) :=
        tsub_le_tsub_left hnum 1
    _ ≤ _ := h
    _ ≤ _ := by
        refine measure_mono ?_
        rintro A ⟨-, hA⟩
        show GaussianMatrix.specNorm (Matrix.of A) ≤ 4 * Real.sqrt s
        linarith

/-! ### Greedy packing -/

private lemma greedy {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (G : Set Ω)
    (D : Ω → Ω → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ) (hD0 : ∀ a, D a a = 0) (hDs : ∀ a b, D a b = D b a)
    (ε : ℝ≥0∞) (hball : ∀ a, μ {x | D x a ≤ ρ} ≤ ε) :
    ∀ k : ℕ, (k : ℝ≥0∞) * ε < μ G →
      ∃ S : Finset Ω, S.card = k ∧ (∀ a ∈ S, a ∈ G) ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ρ < D a b := by
  classical
  intro k
  induction k with
  | zero => intro _; exact ⟨∅, by simp⟩
  | succ k ih =>
    intro hk
    have hk' : (k : ℝ≥0∞) * ε < μ G := by
      refine lt_of_le_of_lt ?_ hk
      gcongr
      exact Nat.le_succ k
    obtain ⟨S, hcard, hSG, hsep⟩ := ih hk'
    have hU : μ (⋃ a ∈ S, {x | D x a ≤ ρ}) ≤ (k : ℝ≥0∞) * ε := by
      calc μ (⋃ a ∈ S, {x | D x a ≤ ρ}) ≤ ∑ a ∈ S, μ {x | D x a ≤ ρ} :=
            measure_biUnion_finset_le _ _
        _ ≤ ∑ _a ∈ S, ε := Finset.sum_le_sum fun a _ => hball a
        _ = (k : ℝ≥0∞) * ε := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
    have hne : ¬ G ⊆ ⋃ a ∈ S, {x | D x a ≤ ρ} := by
      intro hsub
      exact absurd ((measure_mono hsub).trans hU) (not_le.mpr hk')
    obtain ⟨x, hxG, hxU'⟩ := Set.not_subset.mp hne
    have hxU : ∀ a ∈ S, ρ < D x a := by
      intro a ha
      by_contra hcon
      exact hxU' (Set.mem_biUnion ha (not_lt.mp hcon))
    have hxS : x ∉ S := fun hx => by
      have := hxU x hx
      rw [hD0] at this
      linarith
    refine ⟨insert x S, by rw [Finset.card_insert_of_notMem hxS, hcard], ?_, ?_⟩
    · intro a ha
      rcases Finset.mem_insert.mp ha with h | h
      · rw [h]; exact hxG
      · exact hSG a h
    · intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with h | h <;> rcases Finset.mem_insert.mp hb with h' | h'
      · exact absurd (h.trans h'.symm) hab
      · rw [h]; exact hxU b h'
      · rw [h', hDs]; exact hxU a h
      · exact hsep a h b h' hab

/-! ### Assembly -/

/-- The embedding of two blocks of size `s` into `Fin n`. -/
private def emb (s n : ℕ) (h : s + s ≤ n) : Fin s ⊕ Fin s → Fin n :=
  fun c => Fin.castLE h (finSumFinEquiv c)

private lemma emb_injective (s n : ℕ) (h : s + s ≤ n) : Function.Injective (emb s n h) :=
  (Fin.castLE_injective h).comp finSumFinEquiv.injective

private lemma XR_quad_spec {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ⊕ ι → κ) (he : Function.Injective e) (c : ℝ) (hc : 0 ≤ c)
    (A : Matrix ι ι ℝ) (x : κ → ℝ) :
    |x ⬝ᵥ XR e c A *ᵥ x| ≤ c * GaussianMatrix.specNorm A * (x ⬝ᵥ x) :=
  XR_quad e he c hc A x

private lemma ceil_bound (d : ℕ) (hd : 36 ≤ d) :
    (⌈Real.exp ((d : ℝ) / 8)⌉₊ : ℝ) * Real.exp (-(d : ℝ) / 4) < 2⁻¹ := by
  have hd' : (36 : ℝ) ≤ d := by exact_mod_cast hd
  have hE5 : 5 ≤ Real.exp ((d : ℝ) / 8) := by
    have := Real.add_one_le_exp ((d : ℝ) / 8)
    linarith
  have h1 : Real.exp (-(d : ℝ) / 4) = (Real.exp ((d : ℝ) / 8) ^ 2)⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    push_cast
    ring
  have h2 : (⌈Real.exp ((d : ℝ) / 8)⌉₊ : ℝ) < Real.exp ((d : ℝ) / 8) + 1 :=
    Nat.ceil_lt_add_one (Real.exp_pos _).le
  rw [h1, ← div_eq_mul_inv, div_lt_iff₀ (by positivity)]
  nlinarith

private lemma ennreal_bound (d : ℕ) (hd : 36 ≤ d) :
    ((⌈Real.exp ((d : ℝ) / 8)⌉₊ : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(d : ℝ) / 4))
      < 2⁻¹ := by
  have h2 : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal 2⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (by norm_num)]; simp
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), h2,
    ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  exact ceil_bound d hd

private lemma dist_num (n s : ℕ) (hs : 1 ≤ s) (h3 : n ≤ 3 * s) (Dv : ℝ)
    (hD : ((s * s : ℕ) : ℝ) / 8 < Dv) :
    (1 / 12 : ℝ) * n ≤ 2 * (s : ℝ)⁻¹ * Dv := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have h3' : (n : ℝ) ≤ 3 * s := by exact_mod_cast h3
  push_cast at hD
  have h1 : (s : ℝ) / 4 = 2 * (s : ℝ)⁻¹ * ((s : ℝ) * s / 8) := by
    field_simp
    ring
  have h2 : (s : ℝ) / 4 ≤ 2 * (s : ℝ)⁻¹ * Dv := by
    rw [h1]
    exact mul_le_mul_of_nonneg_left hD.le (by positivity)
  linarith

private lemma card_num (n s : ℕ) (h3 : n ≤ 3 * s) :
    (1 / 72 : ℝ) * (n : ℝ) ^ 2 ≤ ((s * s : ℕ) : ℝ) / 8 := by
  have h3' : (n : ℝ) ≤ 3 * s := by exact_mod_cast h3
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  push_cast
  nlinarith

private lemma packing_at (n : ℕ) (hn : 12 ≤ n) :
    ∃ T : Finset (Matrix (Fin n) (Fin n) ℂ),
      Real.exp ((1 / 72 : ℝ) * (n : ℝ) ^ 2) ≤ (T.card : ℝ) ∧
      (∀ X ∈ T, X.IsHermitian ∧ X.trace = 0 ∧
        (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - X).PosSemidef ∧
        (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + X).PosSemidef) ∧
      ∀ X ∈ T, ∀ Y ∈ T, X ≠ Y → (1 / 12 : ℝ) * n ≤ ((X - Y) * (X - Y)).trace.re := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = n / 2 := ⟨_, rfl⟩
  have hs6 : 6 ≤ s := by omega
  have h2s : s + s ≤ n := by omega
  have h3s : n ≤ 3 * s := by omega
  have hd36 : 36 ≤ s * s := by nlinarith
  have hspos : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
  have he := emb_injective s n h2s
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (Real.sqrt s)⁻¹ := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  have hc2 : c ^ 2 = (s : ℝ)⁻¹ := by
    rw [hc, inv_pow, Real.sq_sqrt hspos.le]
  have hc4 : c * (4 * Real.sqrt s) = 4 := by
    rw [hc]; field_simp
  let Xmap : (Fin s → Fin s → ℝ) → Matrix (Fin n) (Fin n) ℂ :=
    fun A => cx (XR (emb s n h2s) c (Matrix.of A))
  let D : (Fin s → Fin s → ℝ) → (Fin s → Fin s → ℝ) → ℝ :=
    fun A B => ∑ i, ∑ j, (A i j - B i j) ^ 2
  have hD0 : ∀ A, D A A = 0 := by intro A; simp [D]
  have hDs : ∀ A B, D A B = D B A := by
    intro A B
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hDnn : ∀ A B, 0 ≤ D A B := fun A B =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  -- the Frobenius distance of the images
  have hdist : ∀ A B, ((Xmap A - Xmap B) * (Xmap A - Xmap B)).trace.re
      = 2 * (s : ℝ)⁻¹ * D A B := by
    intro A B
    simp only [Xmap]
    rw [cx_sub, cx_mul, cx_trace, Complex.ofReal_re, XR_sub, XR_sq_trace _ he, hc2]
    rfl
  -- the greedy family
  have hk : ((⌈Real.exp (((s * s : ℕ) : ℝ) / 8)⌉₊ : ℕ) : ℝ≥0∞)
      * ENNReal.ofReal (Real.exp (-((s * s : ℕ) : ℝ) / 4))
      < (GaussianMatrix.gaussianMatrix s s)
        {A | GaussianMatrix.specNorm (Matrix.of A) ≤ 4 * Real.sqrt s} :=
    lt_of_lt_of_le (ennreal_bound (s * s) hd36) (good_set s (by omega))
  obtain ⟨S, hcard, hSG, hsep⟩ := greedy (GaussianMatrix.gaussianMatrix s s)
    {A | GaussianMatrix.specNorm (Matrix.of A) ≤ 4 * Real.sqrt s} D (((s * s : ℕ) : ℝ) / 8)
    (by positivity) hD0 hDs _ (small_ball s) _ hk
  have hinj : Set.InjOn Xmap (S : Set (Fin s → Fin s → ℝ)) := by
    intro A hA B hB hAB
    by_contra hne
    have h1 := hsep A hA B hB hne
    have h2 := hdist A B
    rw [hAB, sub_self, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re] at h2
    have h3 : 0 < 2 * (s : ℝ)⁻¹ * D A B := by
      have : (0 : ℝ) ≤ ((s * s : ℕ) : ℝ) / 8 := by positivity
      have : 0 < D A B := lt_of_le_of_lt this h1
      positivity
    linarith
  refine ⟨S.image Xmap, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hinj, hcard]
    calc Real.exp ((1 / 72 : ℝ) * (n : ℝ) ^ 2)
        ≤ Real.exp (((s * s : ℕ) : ℝ) / 8) := Real.exp_le_exp.mpr (card_num n s h3s)
      _ ≤ _ := Nat.le_ceil _
  · intro X hX
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hX
    have hAG : GaussianMatrix.specNorm (Matrix.of A) ≤ 4 * Real.sqrt s := hSG A hA
    have hT : (XR (emb s n h2s) c (Matrix.of A))ᵀ = XR (emb s n h2s) c (Matrix.of A) :=
      XR_transpose _ _ _
    refine ⟨cx_isHermitian _ hT, ?_, ?_⟩
    · simp only [Xmap]
      rw [cx_trace, XR_trace _ he]
      simp
    · refine psd_of_real_form _ hT 4 fun x => ?_
      refine (XR_quad_spec _ he c hc0.le (Matrix.of A) x).trans ?_
      have hx : 0 ≤ x ⬝ᵥ x := by
        simp only [dotProduct]
        exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
      refine mul_le_mul_of_nonneg_right ?_ hx
      calc c * GaussianMatrix.specNorm (Matrix.of A) ≤ c * (4 * Real.sqrt s) :=
            mul_le_mul_of_nonneg_left hAG hc0.le
        _ = 4 := hc4
  · intro X hX Y hY hXY
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hX
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hY
    have hAB : A ≠ B := fun h => hXY (by rw [h])
    rw [hdist A B]
    exact dist_num n s (by omega) h3s _ (hsep A hA B hB hAB)

theorem solution :
    ∃ b : ℝ, 0 < b ∧ ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ T : Finset (Matrix (Fin n) (Fin n) ℂ),
        Real.exp (c * (n : ℝ) ^ 2) ≤ (T.card : ℝ) ∧
        (∀ X ∈ T, X.IsHermitian ∧ X.trace = 0 ∧
          (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - X).PosSemidef ∧
          (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + X).PosSemidef) ∧
        ∀ X ∈ T, ∀ Y ∈ T, X ≠ Y → b * n ≤ ((X - Y) * (X - Y)).trace.re :=
  ⟨1 / 12, by norm_num, 1 / 72, by norm_num, 12, fun n hn => packing_at n hn⟩

end

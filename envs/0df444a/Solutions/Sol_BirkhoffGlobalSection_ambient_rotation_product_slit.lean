-- Prove2me | solution 1 for BirkhoffGlobalSection.ambient_rotation_product_slit
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-28T18:38:48.783564+00:00
-- url     : https://prove2.me/submissions/5dfa1185-6b78-4e92-b047-9a9fd72cf9db

import Definitions.Def_BirkhoffGlobalSection_AmbientRotation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

open BirkhoffGlobalSection
open Matrix

set_option autoImplicit false

/-! ### Squared norm and Hermitian pairing on `ℂ²` -/

/-- The squared Euclidean norm on `ℂ²`. -/
private def nsq (v : Fin 2 → ℂ) : ℝ :=
  (v 0).re ^ 2 + (v 0).im ^ 2 + (v 1).re ^ 2 + (v 1).im ^ 2

/-- The Hermitian pairing on `ℂ²`, conjugate-linear in the first slot. -/
private def hp (a b : Fin 2 → ℂ) : ℂ :=
  (starRingEnd ℂ) (a 0) * b 0 + (starRingEnd ℂ) (a 1) * b 1

private lemma nsq_nonneg (v : Fin 2 → ℂ) : 0 ≤ nsq v := by
  unfold nsq; positivity

private lemma nsq_zero : nsq 0 = 0 := by simp [nsq]

private lemma nsq_pos {v : Fin 2 → ℂ} (hv : v ≠ 0) : 0 < nsq v := by
  rcases (nsq_nonneg v).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hv
    unfold nsq at h
    have h1 : (v 0).re ^ 2 = 0 := by
      nlinarith [sq_nonneg (v 0).re, sq_nonneg (v 0).im, sq_nonneg (v 1).re,
        sq_nonneg (v 1).im]
    have h2 : (v 0).im ^ 2 = 0 := by
      nlinarith [sq_nonneg (v 0).re, sq_nonneg (v 0).im, sq_nonneg (v 1).re,
        sq_nonneg (v 1).im]
    have h3 : (v 1).re ^ 2 = 0 := by
      nlinarith [sq_nonneg (v 0).re, sq_nonneg (v 0).im, sq_nonneg (v 1).re,
        sq_nonneg (v 1).im]
    have h4 : (v 1).im ^ 2 = 0 := by
      nlinarith [sq_nonneg (v 0).re, sq_nonneg (v 0).im, sq_nonneg (v 1).re,
        sq_nonneg (v 1).im]
    rw [pow_eq_zero_iff two_ne_zero] at h1 h2 h3 h4
    funext i
    fin_cases i
    · exact Complex.ext h1 h2
    · exact Complex.ext h3 h4

private lemma hp_self_re (w : Fin 2 → ℂ) : (hp w w).re = nsq w := by
  simp only [hp, nsq, Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private lemma hp_mulVec (a b : Fin 2 → ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    hp a (A *ᵥ b) = hp (Aᴴ *ᵥ a) b := by
  simp [hp, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  ring

private lemma hp_smul (a b : Fin 2 → ℂ) (c e : ℂ) :
    hp (c • a) (e • b) = (starRingEnd ℂ) c * e * hp a b := by
  simp [hp]; ring

private lemma hp_smul_right (a b : Fin 2 → ℂ) (e : ℂ) : hp a (e • b) = e * hp a b := by
  simp [hp]; ring

private lemma hp_add_right (a b b' : Fin 2 → ℂ) : hp a (b + b') = hp a b + hp a b' := by
  simp [hp]; ring

private lemma re_hp_ge (a b : Fin 2 → ℂ) : -(nsq a + nsq b) / 2 ≤ (hp a b).re := by
  simp only [hp, nsq, Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg ((a 0).re + (b 0).re), sq_nonneg ((a 0).im + (b 0).im),
    sq_nonneg ((a 1).re + (b 1).re), sq_nonneg ((a 1).im + (b 1).im)]

/-! ### Accretive `2 × 2` matrices -/

/-- Real form of the accretivity estimate for a `2 × 2` determinant. -/
private lemma accretive_real {a₁ a₂ d₁ d₂ p q r s : ℝ} (h1 : 0 < a₁)
    (h2 : (p + r) ^ 2 + (q - s) ^ 2 < 4 * a₁ * d₁)
    (him : a₁ * d₂ + a₂ * d₁ - (p * s + q * r) = 0) :
    0 < a₁ * d₁ - a₂ * d₂ - (p * r - q * s) := by
  have hid : a₁ ^ 2 * (a₁ * d₁ - a₂ * d₂ - (p * r - q * s)) =
      (a₁ ^ 2 + a₂ ^ 2) * (a₁ * d₁ - ((p + r) ^ 2 + (q - s) ^ 2) / 4) +
      (a₁ * (q + s) / 2 - a₂ * (p + r) / 2) ^ 2 +
      (a₁ * (-(p - r)) / 2 - a₂ * (q - s) / 2) ^ 2 -
      a₁ * a₂ * (a₁ * d₂ + a₂ * d₁ - (p * s + q * r)) := by ring
  rw [him, mul_zero, sub_zero] at hid
  have hdet : 0 < a₁ * d₁ - ((p + r) ^ 2 + (q - s) ^ 2) / 4 := by linarith
  have hsq : 0 < a₁ ^ 2 + a₂ ^ 2 := by positivity
  have hpos : 0 < a₁ ^ 2 * (a₁ * d₁ - a₂ * d₂ - (p * r - q * s)) := by
    rw [hid]; positivity
  exact pos_of_mul_pos_right hpos (by positivity)

/-- A `2 × 2` complex matrix with positive definite Hermitian part has its
determinant in the slit plane (entry form). -/
private lemma det_slit_of_accretive (x00 x01 x10 x11 : ℂ) (h1 : 0 < x00.re)
    (h2 : (x01.re + x10.re) ^ 2 + (x01.im - x10.im) ^ 2 < 4 * x00.re * x11.re) :
    x00 * x11 - x01 * x10 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
  by_cases him : x00.re * x11.im + x00.im * x11.re -
      (x01.re * x10.im + x01.im * x10.re) = 0
  · left
    have := accretive_real h1 h2 him
    linarith
  · right
    intro h; apply him; linarith

/-- A `2 × 2` complex matrix whose Hermitian form has positive real part on
nonzero vectors has its determinant in the slit plane. -/
private lemma det_slit_of_pos (X : Matrix (Fin 2) (Fin 2) ℂ)
    (h : ∀ v : Fin 2 → ℂ, v ≠ 0 → 0 < (hp v (X *ᵥ v)).re) :
    X.det ∈ Complex.slitPlane := by
  have ha : 0 < (X 0 0).re := by
    have hne : (![1, 0] : Fin 2 → ℂ) ≠ 0 := by
      intro h0
      have := congrFun h0 0
      simp at this
    have hv := h _ hne
    simpa [hp, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hv
  rw [Matrix.det_fin_two]
  refine det_slit_of_accretive _ _ _ _ ha ?_
  set b : ℂ := ⟨((X 0 1).re + (X 1 0).re) / 2, ((X 0 1).im - (X 1 0).im) / 2⟩ with hb
  have hne : (![-b, ((X 0 0).re : ℂ)] : Fin 2 → ℂ) ≠ 0 := by
    intro h0
    have := congrFun h0 1
    simp at this
    linarith
  have hv := h _ hne
  have key : (hp ![-b, ((X 0 0).re : ℂ)] (X *ᵥ ![-b, ((X 0 0).re : ℂ)])).re =
      (X 0 0).re * ((X 0 0).re * (X 1 1).re -
        (((X 0 1).re + (X 1 0).re) ^ 2 + ((X 0 1).im - (X 1 0).im) ^ 2) / 4) := by
    simp [hp, hb, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_re,
      Complex.mul_im]
    ring
  rw [key] at hv
  have := pos_of_mul_pos_right hv ha.le
  linarith

/-- Dividing by a positive real preserves the slit plane. -/
private lemma slit_of_ofReal_mul {r : ℝ} (hr : 0 < r) {z : ℂ}
    (h : (r : ℂ) * z ∈ Complex.slitPlane) : z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff] at h ⊢
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero] at h
  rcases h with h | h
  · left; exact pos_of_mul_pos_right h hr.le
  · right; intro h0; apply h; rw [h0, mul_zero]

/-! ### The complex core of the bounded-defect estimate -/

/-- Let `P₁, K₁` satisfy the row relation `‖P₁ᴴ x‖² = ‖x‖² + ‖K₁ᴴ x‖²` and `P₂, L₂`
the column relation `‖P₂ u‖² = ‖u‖² + ‖L₂ u‖²`. Then
`det (P₁ P₂ + K₁ L₂) · conj (det P₁) · conj (det P₂)` lies in the slit plane. -/
private lemma core_slit (P₁ K₁ P₂ L₂ : Matrix (Fin 2) (Fin 2) ℂ)
    (hrow : ∀ x : Fin 2 → ℂ, nsq (P₁ᴴ *ᵥ x) = nsq x + nsq (K₁ᴴ *ᵥ x))
    (hcol : ∀ u : Fin 2 → ℂ, nsq (P₂ *ᵥ u) = nsq u + nsq (L₂ *ᵥ u)) :
    (P₁ * P₂ + K₁ * L₂).det * (starRingEnd ℂ) P₁.det * (starRingEnd ℂ) P₂.det ∈
      Complex.slitPlane := by
  -- the complex-linear parts are invertible
  have hd1 : P₁.det ≠ 0 := by
    intro h0
    have h0' : P₁ᴴ.det = 0 := by rw [Matrix.det_conjTranspose, h0, star_zero]
    obtain ⟨x, hx, hPx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0'
    have h1 := hrow x
    rw [hPx, nsq_zero] at h1
    linarith [nsq_pos hx, nsq_nonneg (K₁ᴴ *ᵥ x)]
  have hd2 : P₂.det ≠ 0 := by
    intro h0
    obtain ⟨u, hu, hPu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have h1 := hcol u
    rw [hPu, nsq_zero] at h1
    linarith [nsq_pos hu, nsq_nonneg (L₂ *ᵥ u)]
  -- the accretive matrix
  set X : Matrix (Fin 2) (Fin 2) ℂ := (starRingEnd ℂ) (P₁.det * P₂.det) •
    (P₁.adjugate * (P₁ * P₂ + K₁ * L₂) * P₂.adjugate) with hX
  have hdetX : X.det = ((Complex.normSq (P₁.det * P₂.det) : ℝ) : ℂ) *
      ((P₁ * P₂ + K₁ * L₂).det * (starRingEnd ℂ) P₁.det * (starRingEnd ℂ) P₂.det) := by
    rw [hX, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_adjugate,
      Matrix.det_adjugate, Complex.normSq_eq_conj_mul_self]
    simp only [Fintype.card_fin, map_mul]
    ring
  have hpos : ∀ v : Fin 2 → ℂ, v ≠ 0 → 0 < (hp v (X *ᵥ v)).re := by
    intro v hv
    set x : Fin 2 → ℂ := P₂.det • (P₁.adjugateᴴ *ᵥ v) with hx
    set u : Fin 2 → ℂ := (starRingEnd ℂ) P₁.det • (P₂.adjugate *ᵥ v) with hu
    set w : Fin 2 → ℂ := ((starRingEnd ℂ) P₁.det * P₂.det) • v with hw
    have hPx : P₁ᴴ *ᵥ x = w := by
      funext i
      fin_cases i <;>
        simp [hx, hw, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.adjugate_fin_two,
          Matrix.det_fin_two] <;> ring
    have hPu : P₂ *ᵥ u = w := by
      funext i
      fin_cases i <;>
        simp [hu, hw, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.adjugate_fin_two,
          Matrix.det_fin_two] <;> ring
    have hsplit : hp v (X *ᵥ v) = hp (P₁ᴴ *ᵥ x) (P₂ *ᵥ u) + hp (K₁ᴴ *ᵥ x) (L₂ *ᵥ u) := by
      have e1 : X *ᵥ v = (starRingEnd ℂ) (P₁.det * P₂.det) • (P₁.adjugate *ᵥ
          (P₁ *ᵥ (P₂ *ᵥ (P₂.adjugate *ᵥ v)) + K₁ *ᵥ (L₂ *ᵥ (P₂.adjugate *ᵥ v)))) := by
        rw [hX, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      have lhs : hp v (X *ᵥ v) = (starRingEnd ℂ) (P₁.det * P₂.det) *
          (hp (P₁ᴴ *ᵥ (P₁.adjugateᴴ *ᵥ v)) (P₂ *ᵥ (P₂.adjugate *ᵥ v)) +
            hp (K₁ᴴ *ᵥ (P₁.adjugateᴴ *ᵥ v)) (L₂ *ᵥ (P₂.adjugate *ᵥ v))) := by
        rw [e1, hp_smul_right, hp_mulVec v _ P₁.adjugate, hp_add_right,
          hp_mulVec _ _ P₁, hp_mulVec _ _ K₁]
      have rhs : hp (P₁ᴴ *ᵥ x) (P₂ *ᵥ u) + hp (K₁ᴴ *ᵥ x) (L₂ *ᵥ u) =
          (starRingEnd ℂ) P₂.det * (starRingEnd ℂ) P₁.det *
          (hp (P₁ᴴ *ᵥ (P₁.adjugateᴴ *ᵥ v)) (P₂ *ᵥ (P₂.adjugate *ᵥ v)) +
            hp (K₁ᴴ *ᵥ (P₁.adjugateᴴ *ᵥ v)) (L₂ *ᵥ (P₂.adjugate *ᵥ v))) := by
        rw [hx, hu, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul,
          Matrix.mulVec_smul, hp_smul, hp_smul]
        ring
      rw [lhs, rhs, map_mul]
      ring
    have hcd : (starRingEnd ℂ) P₁.det * P₂.det ≠ 0 :=
      mul_ne_zero ((map_ne_zero _).mpr hd1) hd2
    have hw0 : w ≠ 0 := smul_ne_zero hcd hv
    have hu0 : u ≠ 0 := by
      intro h0; apply hw0; rw [← hPu, h0, Matrix.mulVec_zero]
    have ha := hrow x
    have hb := hcol u
    rw [hPx] at ha hsplit
    rw [hPu] at hb hsplit
    rw [hsplit, Complex.add_re, hp_self_re]
    have h1 := re_hp_ge (K₁ᴴ *ᵥ x) (L₂ *ᵥ u)
    have h2 := nsq_pos hu0
    have h3 := nsq_nonneg x
    linarith
  have hslit := det_slit_of_pos X hpos
  rw [hdetX] at hslit
  have hr : 0 < Complex.normSq (P₁.det * P₂.det) :=
    Complex.normSq_pos.mpr (mul_ne_zero hd1 hd2)
  exact slit_of_ofReal_mul hr hslit

/-! ### Real `4 × 4` matrices and their complex parts -/

/-- The coordinate matrix of a linear map, `toMat Y i k = Y (e_k) i`. -/
private def toMat (Y : Phase →L[ℝ] Phase) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i k => Y (coordinateVector k) i

/-- Complex-linear part `(A + D + i (B - C)) / 2` of a real `4 × 4` matrix. -/
private noncomputable def Pm (Y : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨(Y 0 0 + Y 2 2) / 2, (Y 0 2 - Y 2 0) / 2⟩, ⟨(Y 0 1 + Y 2 3) / 2, (Y 0 3 - Y 2 1) / 2⟩;
     ⟨(Y 1 0 + Y 3 2) / 2, (Y 1 2 - Y 3 0) / 2⟩, ⟨(Y 1 1 + Y 3 3) / 2, (Y 1 3 - Y 3 1) / 2⟩]

/-- Conjugate-linear part `(A - D - i (B + C)) / 2` of a real `4 × 4` matrix. -/
private noncomputable def Km (Y : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨(Y 0 0 - Y 2 2) / 2, -(Y 0 2 + Y 2 0) / 2⟩, ⟨(Y 0 1 - Y 2 3) / 2, -(Y 0 3 + Y 2 1) / 2⟩;
     ⟨(Y 1 0 - Y 3 2) / 2, -(Y 1 2 + Y 3 0) / 2⟩, ⟨(Y 1 1 - Y 3 3) / 2, -(Y 1 3 + Y 3 1) / 2⟩]

/-- The entrywise conjugate of `Km`. -/
private noncomputable def Kb (Y : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨(Y 0 0 - Y 2 2) / 2, (Y 0 2 + Y 2 0) / 2⟩, ⟨(Y 0 1 - Y 2 3) / 2, (Y 0 3 + Y 2 1) / 2⟩;
     ⟨(Y 1 0 - Y 3 2) / 2, (Y 1 2 + Y 3 0) / 2⟩, ⟨(Y 1 1 - Y 3 3) / 2, (Y 1 3 + Y 3 1) / 2⟩]

private lemma acl_eq (Y : Phase →L[ℝ] Phase) : ambientComplexLinearPart Y = Pm (toMat Y) := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

private lemma basis_decomp (v : Phase) :
    v = v 0 • coordinateVector 0 + v 1 • coordinateVector 1 +
      v 2 • coordinateVector 2 + v 3 • coordinateVector 3 := by
  funext i; fin_cases i <;> simp [coordinateVector]

private lemma apply_eq_mulVec (Y : Phase →L[ℝ] Phase) (v : Phase) : Y v = toMat Y *ᵥ v := by
  conv_lhs => rw [basis_decomp v]
  funext i
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, toMat,
    Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.of_apply]
  ring

private lemma toMat_comp (Φ M : Phase →L[ℝ] Phase) :
    toMat (Φ.comp M) = toMat Φ * toMat M := by
  ext i k
  simp only [toMat, Matrix.of_apply, ContinuousLinearMap.comp_apply, Matrix.mul_apply]
  rw [apply_eq_mulVec Φ (M (coordinateVector k))]
  simp [Matrix.mulVec, dotProduct, toMat]

private lemma symp_mat {Y : Phase →L[ℝ] Phase}
    (hY : ∀ u v : Phase,
      Y u ⬝ᵥ TangentialHessian.qI.mulVec (Y v) = u ⬝ᵥ TangentialHessian.qI.mulVec v) :
    (toMat Y).transpose * TangentialHessian.qI * toMat Y = TangentialHessian.qI := by
  ext k l
  have h := hY (coordinateVector k) (coordinateVector l)
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, toMat, Matrix.of_apply]
  simp only [dotProduct, Matrix.mulVec] at h
  rw [h]
  simp [coordinateVector]

private lemma qI_mul_qI : TangentialHessian.qI * TangentialHessian.qI = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [TangentialHessian.qI, Matrix.mul_apply, Fin.sum_univ_four]

/-- The column relations `Yᵀ J Y = J` imply the row relations `Y J Yᵀ = J`. -/
private lemma row_rel {Y : Matrix (Fin 4) (Fin 4) ℝ}
    (h1 : Y.transpose * TangentialHessian.qI * Y = TangentialHessian.qI) :
    Y.transpose.transpose * TangentialHessian.qI * Y.transpose = TangentialHessian.qI := by
  rw [Matrix.transpose_transpose]
  set J := TangentialHessian.qI with hJ
  have hJJ : J * J = -1 := qI_mul_qI
  have h2 : (-(J * Y.transpose * J)) * Y = 1 := by
    calc (-(J * Y.transpose * J)) * Y = -(J * (Y.transpose * J * Y)) := by
          simp [Matrix.mul_assoc]
      _ = -(J * J) := by rw [h1]
      _ = 1 := by rw [hJJ, neg_neg]
  have h3 : Y * (-(J * Y.transpose * J)) = 1 := mul_eq_one_comm.mp h2
  have h4 : Y * J * Y.transpose * J = -1 := by
    calc Y * J * Y.transpose * J = -(Y * (-(J * Y.transpose * J))) := by
          simp [Matrix.mul_assoc]
      _ = -1 := by rw [h3]
  calc Y * J * Y.transpose = -(Y * J * Y.transpose * J * J) := by
        rw [Matrix.mul_assoc (Y * J * Y.transpose) J J, hJJ]; simp
    _ = J := by rw [h4]; simp

/-- The complex-linear part of a product. -/
private lemma Pm_mul (Y Z : Matrix (Fin 4) (Fin 4) ℝ) :
    Pm (Y * Z) = Pm Y * Pm Z + Km Y * Kb Z := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [Pm, Km, Kb, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

private lemma Pm_transpose (Y : Matrix (Fin 4) (Fin 4) ℝ) : Pm Y.transpose = (Pm Y)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [Pm, Matrix.conjTranspose_apply] <;> ring

private lemma Kb_transpose (Y : Matrix (Fin 4) (Fin 4) ℝ) : Kb Y.transpose = (Km Y)ᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [Kb, Km, Matrix.conjTranspose_apply] <;> ring

/-- For a symplectic matrix, `‖P u‖² = ‖u‖² + ‖K̄ u‖²`. -/
private lemma col_identity {Y : Matrix (Fin 4) (Fin 4) ℝ}
    (hY : Y.transpose * TangentialHessian.qI * Y = TangentialHessian.qI) (u : Fin 2 → ℂ) :
    nsq (Pm Y *ᵥ u) = nsq u + nsq (Kb Y *ᵥ u) := by
  set x : Fin 4 → ℝ := ![(u 0).re, (u 1).re, -(u 0).im, -(u 1).im] with hx
  have key : nsq (Pm Y *ᵥ u) - nsq (Kb Y *ᵥ u) =
      -(x ⬝ᵥ (Y.transpose * TangentialHessian.qI * Y) *ᵥ (TangentialHessian.qI *ᵥ x)) := by
    simp [nsq, Pm, Kb, hx, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_four,
      Matrix.mul_apply, TangentialHessian.qI, Complex.mul_re, Complex.mul_im]
    ring
  rw [hY] at key
  have hq : x ⬝ᵥ TangentialHessian.qI *ᵥ (TangentialHessian.qI *ᵥ x) = -nsq u := by
    simp [nsq, hx, Matrix.mulVec, dotProduct, Fin.sum_univ_four, TangentialHessian.qI]
    ring
  linarith

theorem solution (Φ M : Phase →L[ℝ] Phase)
    (hΦ : ∀ u v : Phase,
      Φ u ⬝ᵥ TangentialHessian.qI.mulVec (Φ v) = u ⬝ᵥ TangentialHessian.qI.mulVec v)
    (hM : ∀ u v : Phase,
      M u ⬝ᵥ TangentialHessian.qI.mulVec (M v) = u ⬝ᵥ TangentialHessian.qI.mulVec v) :
    ambientRotationDet (Φ.comp M) * (starRingEnd ℂ) (ambientRotationDet Φ) *
      (starRingEnd ℂ) (ambientRotationDet M) ∈ Complex.slitPlane := by
  unfold ambientRotationDet
  simp only [acl_eq, toMat_comp, Pm_mul]
  apply core_slit
  · intro x
    have h := col_identity (row_rel (symp_mat hΦ)) x
    rwa [Pm_transpose, Kb_transpose] at h
  · exact col_identity (symp_mat hM)

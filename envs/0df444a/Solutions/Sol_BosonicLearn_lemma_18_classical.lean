-- Prove2me | solution 1 for BosonicLearn.lemma_18_classical
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T21:39:05.144263+00:00
-- url     : https://prove2.me/submissions/34fbaaf0-87e3-42d3-8a6e-299bec9e79a5

import Mathlib
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_BosonicLearn_IsGaussianState
import Theorems.Thm_BosonicLearn_classical_displacement_bound
import Theorems.Thm_BosonicLearn_classical_mixture_overlap_bound
import Theorems.Thm_BosonicLearn_gaussian_shift_overlap
import Theorems.Thm_BosonicLearn_gaussianState_exists_of_le
import Theorems.Thm_BosonicLearn_traceDist_triangle

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14
open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

open BosonicLearn

/-!
# Lemma 18 for classical covariances (first-moment perturbation, constant `1/√2`)

With `T = S - ½·1 ⪰ 0`, `δ = μ' - μ`, `w = S⁻¹ δ`, the shift splits as `δ = T w + ½ w`.

* `gauss_char`: a Gaussian state `ρ(μ₀, S)` has characteristic function
  `charFun N(μ₀ ∘ idx, T ∘ idx) · e^{-|ξ|²/4}` (interleaved coordinates through `idx`).
* An intermediate Gaussian state `σ = ρ(μ + T w, S)` exists (`gaussianState_exists_of_le`).
* `ρ → σ`: `gaussian_shift_overlap` and `classical_mixture_overlap_bound` give
  `D(σ, ρ) ≤ √(wᵀTw)/√(2π)`.
* `σ → ρ'`: `classical_displacement_bound` with `d = ½ w ∘ idx` gives `D(ρ', σ) ≤ √(¼ wᵀw)/√2`.
* `scalar_bound`: `√(B/2)/√2 + √A/√(2π) ≤ √(A+B)/√2` with `A = wᵀTw`, `B = ½ wᵀw`,
  and `A + B = wᵀSw = δᵀS⁻¹δ`.
-/

noncomputable section

/-- Grouped index of an interleaved quadrature index. -/
private def idx {n : ℕ} (a : Fin n × Fin 2) : Fin n ⊕ Fin n :=
  if a.2 = 0 then Sum.inl a.1 else Sum.inr a.1

/-- `idx` as an equivalence. -/
private def idxE (n : ℕ) : Fin n × Fin 2 ≃ Fin n ⊕ Fin n where
  toFun := idx
  invFun := Sum.elim (fun j => (j, 0)) (fun j => (j, 1))
  left_inv := by
    rintro ⟨j, k⟩
    fin_cases k <;> simp [idx]
  right_inv := by
    rintro (j | j) <;> simp [idx]

private lemma idxE_apply {n : ℕ} (a : Fin n × Fin 2) : idxE n a = idx a := rfl

private lemma sum_idx {n : ℕ} (f : Fin n ⊕ Fin n → ℝ) :
    ∑ a : Fin n × Fin 2, f (idx a) = ∑ x, f x :=
  Equiv.sum_comp (idxE n) f

private lemma idx_inj {n : ℕ} (a b : Fin n × Fin 2) : idx a = idx b ↔ a = b :=
  (idxE n).injective.eq_iff

/-- Reindexed matrix-vector product. -/
private lemma submatrix_mulVec_idx {n : ℕ} (T : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (w : Fin n ⊕ Fin n → ℝ) (a : Fin n × Fin 2) :
    (T.submatrix idx idx *ᵥ fun b => w (idx b)) a = (T *ᵥ w) (idx a) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
  exact sum_idx fun x => T (idx a) x * w x

/-- The characteristic function of a Gaussian state with classical covariance, as the
characteristic function of the mixing Gaussian measure times the vacuum factor. -/
private lemma gauss_char {n : ℕ} (ρ : State (Occupation (Fin n))) (μ : Fin n ⊕ Fin n → ℝ)
    (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (hS : (S - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosSemidef)
    (h : IsGaussianState ρ μ S) (ξ : Fin n × Fin 2 → ℝ) :
    oscillatorCharacteristic ρ.coefficients ξ =
      charFun (multivariateGaussian (WithLp.toLp 2 (fun a => μ (idx a)))
        ((S - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).submatrix
          (idx (n := n)) idx))
        (WithLp.toLp 2 ξ) * ((Real.exp (-(∑ a, ξ a ^ 2) / 4) : ℝ) : ℂ) := by
  have hG : GaussianAt ρ.coefficients (fun a => μ (idx a)) (fun a b => 2 * S (idx a) (idx b)) := h
  have hT := hS.submatrix (idx (n := n))
  set T' := (S - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).submatrix
    (idx (n := n)) idx with hT'
  have hc := charFun_multivariateGaussian (μ := WithLp.toLp 2 (fun a => μ (idx a))) hT
    (WithLp.toLp 2 ξ)
  have h2 : inner ℝ (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin n × Fin 2))
      (WithLp.toLp 2 (fun a => μ (idx a))) = meanForm (fun a => μ (idx a)) ξ := by
    simp [meanForm, PiLp.inner_apply, mul_comm]
  have h3 : ξ ⬝ᵥ T' *ᵥ ξ = varianceForm T' ξ := by
    simp only [varianceForm, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hv : varianceForm (fun a b => 2 * S (idx a) (idx b)) ξ =
      2 * varianceForm T' ξ + ∑ a, ξ a ^ 2 := by
    have h1 : ∀ a : Fin n × Fin 2, ∑ b, ξ a * (2 * S (idx a) (idx b)) * ξ b =
        2 * ∑ b, ξ a * T' a b * ξ b + ξ a ^ 2 := by
      intro a
      have h4 : ξ a ^ 2 = ∑ b, ξ a * (if a = b then 1 else 0) * ξ b := by
        simp [sq]
      rw [h4, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [hT', Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.one_apply, idx_inj]
      ring
    simp only [varianceForm]
    rw [Finset.sum_congr rfl fun a _ => h1 a, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hG.2 ξ, hc, h2]
  simp only [h3]
  rw [Complex.ofReal_exp, ← Complex.exp_add, hv]
  congr 1
  push_cast
  ring

/-- The scalar inequality behind the optimal split of the shift. -/
private lemma scalar_bound (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Real.sqrt (B / 2) / Real.sqrt 2 + Real.sqrt A / Real.sqrt (2 * Real.pi) ≤
      Real.sqrt (A + B) / Real.sqrt 2 := by
  have h2 : Real.sqrt (B / 2) / Real.sqrt 2 = Real.sqrt B / 2 := by
    rw [Real.sqrt_div hB, div_div, Real.mul_self_sqrt (by norm_num)]
  have hpi : 2 ≤ Real.sqrt (2 * Real.pi) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [Real.pi_gt_three]
  have h3 : Real.sqrt A / Real.sqrt (2 * Real.pi) ≤ Real.sqrt A / 2 :=
    div_le_div_of_nonneg_left (Real.sqrt_nonneg A) (by norm_num) hpi
  have h4 : (Real.sqrt A + Real.sqrt B) / 2 ≤ Real.sqrt (A + B) / Real.sqrt 2 := by
    rw [← Real.sqrt_div (by positivity)]
    apply Real.le_sqrt_of_sq_le
    nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB, sq_nonneg (Real.sqrt A - Real.sqrt B)]
  rw [h2]
  linarith

theorem solution {n : ℕ} (ρ ρ' : State (Occupation (Fin n))) (μ μ' : Fin n ⊕ Fin n → ℝ)
    (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (hS : (S - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosSemidef)
    (h : IsGaussianState ρ μ S) (h' : IsGaussianState ρ' μ' S) :
    traceDist ρ'.coefficients ρ.coefficients ≤
      ENNReal.ofReal (Real.sqrt ((μ' - μ) ⬝ᵥ (S⁻¹ *ᵥ (μ' - μ))) / Real.sqrt 2) := by
  -- `S = T + ½·1` is positive definite, hence invertible
  have hSpd : S.PosDef := by
    have h1 := Matrix.PosDef.posSemidef_add hS
      ((Matrix.PosDef.one (n := Fin n ⊕ Fin n) (R := ℝ)).smul (show (0 : ℝ) < 1 / 2 by norm_num))
    rwa [sub_add_cancel] at h1
  have hSinv : S * S⁻¹ = 1 :=
    Matrix.mul_nonsing_inv S ((Matrix.isUnit_iff_isUnit_det S).mp hSpd.isUnit)
  set T := S - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) with hTdef
  set δ := μ' - μ with hδ
  set w := S⁻¹ *ᵥ δ with hw
  have hSw : S *ᵥ w = δ := by
    rw [hw, Matrix.mulVec_mulVec, hSinv, Matrix.one_mulVec]
  -- the split `δ = T w + ½ w`
  have hsplit : T *ᵥ w + (1 / 2 : ℝ) • w = δ := by
    rw [← hSw, hTdef, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_add_cancel]
  -- the intermediate Gaussian state with mean `μ + T w`
  obtain ⟨σ, hσ⟩ := gaussianState_exists_of_le ρ μ S h (μ + T *ᵥ w) S
    (by rw [sub_self]; exact Matrix.PosSemidef.zero)
  have hT' := hS.submatrix (idx (n := n))
  -- step 1: `ρ → σ`, a shift of the mixing measure in the range of `T`
  obtain ⟨κ, hκ1, hκ2, hκ3⟩ := gaussian_shift_overlap
    (WithLp.toLp 2 (fun a : Fin n × Fin 2 => μ (idx a)))
    (T.submatrix (idx (n := n)) idx) hT' (fun a => w (idx a))
  have hmean : WithLp.toLp 2 (fun a : Fin n × Fin 2 => μ (idx a)) +
      WithLp.toLp 2 (T.submatrix (idx (n := n)) idx *ᵥ fun a => w (idx a)) =
      WithLp.toLp 2 (fun a : Fin n × Fin 2 => (μ + T *ᵥ w) (idx a)) := by
    rw [← WithLp.toLp_add]
    congr 1
    funext a
    simp only [Pi.add_apply, submatrix_mulVec_idx]
  rw [hmean] at hκ2
  have step3 : traceDist σ.coefficients ρ.coefficients ≤
      ENNReal.ofReal (1 - (κ Set.univ).toReal) :=
    classical_mixture_overlap_bound _ _ κ hκ1 hκ2 ρ σ (gauss_char ρ μ S hS h)
      (gauss_char σ _ S hS hσ)
  -- step 2: `σ → ρ'`, a displacement by `½ w`
  have hchar : ∀ ξ : Fin n × Fin 2 → ℝ, oscillatorCharacteristic ρ'.coefficients ξ =
      Complex.exp (Complex.I * (meanForm (fun a : Fin n × Fin 2 => (1 / 2 : ℝ) * w (idx a)) ξ : ℂ)) *
        oscillatorCharacteristic σ.coefficients ξ := by
    intro ξ
    have hG' : GaussianAt ρ'.coefficients (fun a => μ' (idx a))
        (fun a b => 2 * S (idx a) (idx b)) := h'
    have hGσ : GaussianAt σ.coefficients (fun a => (μ + T *ᵥ w) (idx a))
        (fun a b => 2 * S (idx a) (idx b)) := hσ
    rw [hG'.2 ξ, hGσ.2 ξ, ← Complex.exp_add]
    congr 1
    have hm : meanForm (fun a : Fin n × Fin 2 => (1 / 2 : ℝ) * w (idx a)) ξ +
        meanForm (fun a : Fin n × Fin 2 => (μ + T *ᵥ w) (idx a)) ξ =
        meanForm (fun a : Fin n × Fin 2 => μ' (idx a)) ξ := by
      unfold meanForm
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      have h1 := congrFun hsplit (idx a)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hδ, Pi.sub_apply] at h1 ⊢
      linear_combination ξ a * h1
    rw [← hm]
    push_cast
    ring
  have step4 : traceDist ρ'.coefficients σ.coefficients ≤
      ENNReal.ofReal (Real.sqrt (∑ a : Fin n × Fin 2, ((1 / 2 : ℝ) * w (idx a)) ^ 2) /
        Real.sqrt 2) :=
    classical_displacement_bound
      (multivariateGaussian (WithLp.toLp 2 (fun a : Fin n × Fin 2 => (μ + T *ᵥ w) (idx a)))
        (T.submatrix (idx (n := n)) idx))
      σ ρ' (fun a => (1 / 2 : ℝ) * w (idx a)) (gauss_char σ _ S hS hσ) hchar
  -- the quantities `A = wᵀ T w` and `B = ½ wᵀ w`
  have hA0 : 0 ≤ w ⬝ᵥ T *ᵥ w := by simpa using hS.dotProduct_mulVec_nonneg w
  have hB0 : 0 ≤ (1 / 2 : ℝ) * (w ⬝ᵥ w) := by
    have h1 : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg fun x _ => mul_self_nonneg (w x)
    positivity
  have hAB : w ⬝ᵥ T *ᵥ w + (1 / 2 : ℝ) * (w ⬝ᵥ w) = δ ⬝ᵥ S⁻¹ *ᵥ δ := by
    rw [← hw, dotProduct_comm δ w]
    conv_rhs => rw [← hsplit]
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hAeq : (fun a : Fin n × Fin 2 => w (idx a)) ⬝ᵥ
      T.submatrix (idx (n := n)) idx *ᵥ (fun a => w (idx a)) = w ⬝ᵥ T *ᵥ w := by
    simp only [dotProduct, submatrix_mulVec_idx]
    exact sum_idx fun x => w x * (T *ᵥ w) x
  have hdsq : ∑ a : Fin n × Fin 2, ((1 / 2 : ℝ) * w (idx a)) ^ 2 =
      (1 / 2 : ℝ) * (w ⬝ᵥ w) / 2 := by
    rw [sum_idx fun x => ((1 / 2 : ℝ) * w x) ^ 2]
    simp only [dotProduct, Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hAeq] at hκ3
  rw [hdsq] at step4
  calc traceDist ρ'.coefficients ρ.coefficients
      ≤ traceDist ρ'.coefficients σ.coefficients + traceDist σ.coefficients ρ.coefficients :=
        traceDist_triangle _ _ _
    _ ≤ ENNReal.ofReal (Real.sqrt ((1 / 2 : ℝ) * (w ⬝ᵥ w) / 2) / Real.sqrt 2) +
          ENNReal.ofReal (Real.sqrt (w ⬝ᵥ T *ᵥ w) / Real.sqrt (2 * Real.pi)) :=
        add_le_add step4 (step3.trans (ENNReal.ofReal_le_ofReal (by linarith)))
    _ = ENNReal.ofReal (Real.sqrt ((1 / 2 : ℝ) * (w ⬝ᵥ w) / 2) / Real.sqrt 2 +
          Real.sqrt (w ⬝ᵥ T *ᵥ w) / Real.sqrt (2 * Real.pi)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal (Real.sqrt (δ ⬝ᵥ S⁻¹ *ᵥ δ) / Real.sqrt 2) :=
        ENNReal.ofReal_le_ofReal (by rw [← hAB]; exact scalar_bound _ _ hA0 hB0)

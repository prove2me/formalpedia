-- Prove2me | solution 1 for BoydADMM.ModelFit.lasso_block_zero_test_corrected
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:00:41.467989+00:00
-- url     : https://prove2.me/submissions/3daeb6a8-3282-41e3-a90e-5c6c3b63a9fc

import Mathlib
import Definitions.Def_BoydADMM_ModelFit_Basic

open Matrix


namespace BoydADMM.ModelFit

lemma gl_tel_tel {m n k : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (x : EuclideanSpace ℝ (Fin k)) :
    Matrix.toEuclideanLin M (Matrix.toEuclideanLin N x) = Matrix.toEuclideanLin (M * N) x := by
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]

lemma gl_inner_tel {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (Matrix.toEuclideanLin A x) y = inner ℝ x (Matrix.toEuclideanLin Aᵀ y) := by
  have h := Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
  rw [conjTranspose_eq_transpose_of_trivial] at h
  rw [h, LinearMap.adjoint_inner_right]

lemma gl_tel_ridge {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (ν : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin (P + ν • (1 : Matrix (Fin n) (Fin n) ℝ)) x =
      Matrix.toEuclideanLin P x + ν • x := by
  rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply]
  simp

lemma gl_posDef {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (ν : ℝ) (hν : 0 < ν) :
    (Aᵀ * A + ν • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
  have h1 : (Aᵀ * A).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self A
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  exact Matrix.PosDef.posSemidef_add h1 (Matrix.PosDef.one.smul hν)

lemma gl_inv_mul {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (ν : ℝ) (hν : 0 < ν) :
    (Aᵀ * A + ν • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ * (Aᵀ * A + ν • (1 : Matrix (Fin n) (Fin n) ℝ)) = 1 ∧
    (Aᵀ * A + ν • (1 : Matrix (Fin n) (Fin n) ℝ)) * (Aᵀ * A + ν • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ = 1 := by
  have hd : IsUnit (Aᵀ * A + ν • (1 : Matrix (Fin n) (Fin n) ℝ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (gl_posDef A ν hν).isUnit
  exact ⟨Matrix.nonsing_inv_mul _ hd, Matrix.mul_nonsing_inv _ hd⟩

lemma gl_unique_of_growth {E : Type*} [NormedAddCommGroup E] (f : E → ℝ) (x0 : E) (c : ℝ)
    (hc : 0 < c) (hg : ∀ y, f x0 + c * ‖y - x0‖ ^ 2 ≤ f y) (x : E) :
    IsMinOn f Set.univ x ↔ x = x0 := by
  rw [isMinOn_iff]
  constructor
  · intro hx
    have h1 := hx x0 (Set.mem_univ x0)
    have h2 := hg x
    have h3 : c * ‖x - x0‖ ^ 2 ≤ 0 := by linarith
    have h4 : ‖x - x0‖ ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg ‖x - x0‖]) (sq_nonneg _)
    have : ‖x - x0‖ = 0 := by simpa using h4
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  · rintro rfl y _
    have := hg y
    nlinarith [sq_nonneg ‖y - x‖]

lemma gl_small_t (a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B) : ∃ t : ℝ, 0 < t ∧ B * t ^ 2 < a * t := by
  refine ⟨a / (B + 1), by positivity, ?_⟩
  have hB1 : 0 < B + 1 := by linarith
  rw [div_pow, mul_div_assoc', mul_div_assoc']
  rw [show B * a ^ 2 / (B + 1) ^ 2 = (B / (B + 1)) * (a * (a / (B + 1))) by field_simp]
  rw [show a * a / (B + 1) = a * (a / (B + 1)) by ring]
  have h1 : B / (B + 1) < 1 := by rw [div_lt_one hB1]; linarith
  have h2 : 0 < a * (a / (B + 1)) := by positivity
  nlinarith

lemma gl_quad_expand {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin m))
    (x y : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanLin A y - v‖ ^ 2 = ‖Matrix.toEuclideanLin A x - v‖ ^ 2 +
      2 * inner ℝ (Matrix.toEuclideanLin Aᵀ (Matrix.toEuclideanLin A x - v)) (y - x) +
      ‖Matrix.toEuclideanLin A (y - x)‖ ^ 2 := by
  have e1 : Matrix.toEuclideanLin A y - v =
      (Matrix.toEuclideanLin A x - v) + Matrix.toEuclideanLin A (y - x) := by
    rw [map_sub]; abel
  rw [e1, norm_add_sq_real, real_inner_comm (Matrix.toEuclideanLin A (y - x)), gl_inner_tel,
    real_inner_comm]

lemma gl_norm_expand {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    ‖y‖ ^ 2 = ‖x‖ ^ 2 + 2 * inner ℝ x (y - x) + ‖y - x‖ ^ 2 := by
  have : y = x + (y - x) := by abel
  conv_lhs => rw [this]
  rw [norm_add_sq_real]

lemma gl_ridgeSol_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (ν : ℝ) (hν : 0 < ν)
    (v : EuclideanSpace ℝ (Fin m)) :
    Matrix.toEuclideanLin Aᵀ (Matrix.toEuclideanLin A (ridgeSol A ν v)) + ν • ridgeSol A ν v =
      Matrix.toEuclideanLin Aᵀ v := by
  rw [gl_tel_tel, ← gl_tel_ridge, ridgeSol, gl_tel_tel, ← Matrix.mul_assoc,
    (gl_inv_mul A ν hν).2, Matrix.one_mul]

lemma gl_eq_ridgeSol {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (ν : ℝ) (hν : 0 < ν)
    (v : EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n))
    (hx : Matrix.toEuclideanLin Aᵀ (Matrix.toEuclideanLin A x) + ν • x =
      Matrix.toEuclideanLin Aᵀ v) : x = ridgeSol A ν v := by
  rw [gl_tel_tel, ← gl_tel_ridge] at hx
  have := congrArg (Matrix.toEuclideanLin ((Aᵀ * A + ν • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹)) hx
  rw [gl_tel_tel, gl_tel_tel, (gl_inv_mul A ν hν).1] at this
  simpa [ridgeSol] using this

/-- exact expansion of the group lasso objective around a stationary point. -/
lemma gl_obj_expand {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin m))
    (ρ lam ν : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (hx : Matrix.toEuclideanLin Aᵀ (Matrix.toEuclideanLin A x) + ν • x =
      Matrix.toEuclideanLin Aᵀ v) (hl : lam = ρ * ν * ‖x‖) (y : EuclideanSpace ℝ (Fin n)) :
    groupLassoObj ρ lam A v y = groupLassoObj ρ lam A v x +
      ρ / 2 * ‖Matrix.toEuclideanLin A (y - x)‖ ^ 2 +
      ρ * ν * (‖x‖ * ‖y‖ - inner ℝ x y) := by
  unfold groupLassoObj
  rw [gl_quad_expand A v x y]
  have hg : Matrix.toEuclideanLin Aᵀ (Matrix.toEuclideanLin A x - v) = -(ν • x) := by
    rw [map_sub, ← hx]; abel
  rw [hg, inner_neg_left, inner_smul_left, inner_sub_right, real_inner_self_eq_norm_sq, hl]
  simp only [conj_trivial]
  ring

lemma gl_obj_zero_diff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin m))
    (ρ : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    ρ / 2 * ‖Matrix.toEuclideanLin A y - v‖ ^ 2 = ρ / 2 * ‖Matrix.toEuclideanLin A 0 - v‖ ^ 2 +
      ρ / 2 * ‖Matrix.toEuclideanLin A y‖ ^ 2 - ρ * inner ℝ y (Matrix.toEuclideanLin Aᵀ v) := by
  rw [gl_quad_expand A v 0 y, map_zero, zero_sub, map_neg, inner_neg_left, sub_zero,
    real_inner_comm y]
  ring

lemma gl_inner_eq_sum {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x y = ∑ j, x j * y j := by
  simp [PiLp.inner_apply, mul_comm]

lemma gl_l1_single {n : ℕ} (j : Fin n) (t c : ℝ) :
    l1norm (t • EuclideanSpace.single j c) = |t| * |c| := by
  simp only [l1norm, PiLp.smul_apply, EuclideanSpace.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
  simp [abs_mul]

theorem zero_test_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin m)) (ρ lam : ℝ) (hρ : 0 < ρ) (hlam : 0 < lam) :
    IsMinOn (fun x : EuclideanSpace ℝ (Fin n) =>
        ρ / 2 * ‖Matrix.toEuclideanLin A x - v‖ ^ 2 + lam * l1norm x) Set.univ 0 ↔
      ∀ j, |Matrix.toEuclideanLin Aᵀ v j| ≤ lam / ρ := by
  set w := Matrix.toEuclideanLin Aᵀ v with hw
  have hl0 : l1norm (0 : EuclideanSpace ℝ (Fin n)) = 0 := by simp [l1norm]
  rw [isMinOn_iff]
  constructor
  · intro hmin j
    by_contra hcon
    push_neg at hcon
    have hwj : 0 < |w j| := lt_trans (by positivity) hcon
    have ha : 0 < ρ * |w j| ^ 2 - lam * |w j| := by
      have : lam < ρ * |w j| := by rwa [div_lt_iff₀ hρ, mul_comm] at hcon
      nlinarith
    set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j (w j)
    obtain ⟨t, ht, htB⟩ := gl_small_t _ (ρ / 2 * ‖Matrix.toEuclideanLin A e‖ ^ 2) ha
      (by positivity)
    have h := hmin (t • e) (Set.mem_univ _)
    rw [gl_obj_zero_diff A v ρ (t • e), hl0, gl_l1_single, abs_of_pos ht, map_smul,
      norm_smul, inner_smul_left, EuclideanSpace.inner_single_left] at h
    simp only [conj_trivial, Real.norm_eq_abs, abs_of_pos ht] at h
    have hsq : w j * w j = |w j| ^ 2 := by rw [sq_abs]; ring
    rw [← hw, hsq, mul_pow] at h
    nlinarith
  · intro hj y _
    rw [gl_obj_zero_diff A v ρ y, hl0, ← hw]
    have : ρ * inner ℝ y w ≤ lam * l1norm y := by
      rw [gl_inner_eq_sum, l1norm, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum (fun j _ => ?_)
      have h1 : y j * w j ≤ |y j| * |w j| := by rw [← abs_mul]; exact le_abs_self _
      have h2 : ρ * |w j| ≤ lam := by
        have := mul_le_mul_of_nonneg_left (hj j) hρ.le
        rwa [mul_div_cancel₀ _ hρ.ne'] at this
      nlinarith [abs_nonneg (y j)]
    nlinarith [sq_nonneg ‖Matrix.toEuclideanLin A y‖]

end BoydADMM.ModelFit

open BoydADMM.ModelFit


theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin m)) (ρ lam : ℝ) (hρ : 0 < ρ) (hlam : 0 < lam) :
    IsMinOn (fun x : EuclideanSpace ℝ (Fin n) =>
        ρ / 2 * ‖Matrix.toEuclideanLin A x - v‖ ^ 2 + lam * l1norm x) Set.univ 0 ↔
      ∀ j, |Matrix.toEuclideanLin Aᵀ v j| ≤ lam / ρ := by
  exact zero_test_core A v ρ lam hρ hlam

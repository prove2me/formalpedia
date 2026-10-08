-- Prove2me | solution 1 for BoydADMM.ModelFit.lasso_z_update_soft_threshold
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:57:11.757719+00:00
-- url     : https://prove2.me/submissions/8a024026-9578-4a42-b35d-3c6bc562f2c0

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

lemma gl_sep_growth {n : ℕ} (φ : ℝ → ℝ) (K : ℝ) (c s : EuclideanSpace ℝ (Fin n))
    (h1 : ∀ j t, φ (s j) + K * (s j - c j) ^ 2 + K * (t - s j) ^ 2 ≤ φ t + K * (t - c j) ^ 2)
    (y : EuclideanSpace ℝ (Fin n)) :
    ((∑ j, φ (s j)) + K * ‖s - c‖ ^ 2) + K * ‖y - s‖ ^ 2 ≤ (∑ j, φ (y j)) + K * ‖y - c‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun j _ => h1 j (y j))

lemma gl_soft_1d (lam K κ c t : ℝ) (hK : 0 < K) (hκ : 0 < κ) (hl : lam = 2 * K * κ) :
    lam * |BoydADMM.Prox.softThreshold κ c| + K * (BoydADMM.Prox.softThreshold κ c - c) ^ 2 +
      K * (t - BoydADMM.Prox.softThreshold κ c) ^ 2 ≤ lam * |t| + K * (t - c) ^ 2 := by
  subst hl
  unfold BoydADMM.Prox.softThreshold
  split_ifs with h1 h2
  · rw [abs_of_pos (by linarith : (0:ℝ) < c - κ)]
    have := le_abs_self t
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ 2 * K * κ)]
  · rw [abs_of_neg (by linarith : c + κ < 0)]
    have := neg_abs_le t
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ 2 * K * κ)]
  · rw [abs_zero]
    have h3 : |c| ≤ κ := abs_le.mpr ⟨by linarith, by linarith⟩
    have h4 : c * t ≤ κ * |t| := by
      calc c * t ≤ |c * t| := le_abs_self _
        _ = |c| * |t| := abs_mul _ _
        _ ≤ κ * |t| := mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left h4 hK.le]

lemma gl_svm_1d (N : ℕ) (hN : 0 < N) (ρ c t : ℝ) (hρ : 0 < ρ) :
    max ((N : ℝ) * shiftedSoftThreshold N ρ c + 1) 0 +
      ρ / 2 * (shiftedSoftThreshold N ρ c - c) ^ 2 +
      ρ / 2 * (t - shiftedSoftThreshold N ρ c) ^ 2 ≤
      max ((N : ℝ) * t + 1) 0 + ρ / 2 * (t - c) ^ 2 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hNN : (N : ℝ) * (1 / N) = 1 := mul_one_div_cancel hN'.ne'
  have hρρ : ρ * (N / ρ) = N := by field_simp
  -- key subgradient inequality
  suffices key : ρ * (c - shiftedSoftThreshold N ρ c) * (t - shiftedSoftThreshold N ρ c) +
      max ((N : ℝ) * shiftedSoftThreshold N ρ c + 1) 0 ≤ max ((N : ℝ) * t + 1) 0 by
    nlinarith
  unfold shiftedSoftThreshold
  split_ifs with h1 h2
  · -- s = c - N/ρ, Ns + 1 > 0
    have hs : 0 < (N : ℝ) * (c - N / ρ) + 1 := by
      have : -1 / (N : ℝ) < c - N / ρ := by linarith
      have := mul_lt_mul_of_pos_left this hN'
      rw [show (N : ℝ) * (-1 / N) = -1 by rw [div_eq_mul_one_div, ← mul_assoc, mul_comm (N:ℝ) (-1), mul_assoc, hNN]; ring] at this
      linarith
    rw [max_eq_left hs.le]
    have e : ρ * (c - (c - N / ρ)) = N := by rw [sub_sub_cancel, hρρ]
    rw [e]
    have := le_max_left ((N : ℝ) * t + 1) 0
    nlinarith
  · have hs : (N : ℝ) * c + 1 < 0 := by
      have := mul_lt_mul_of_pos_left h2 hN'
      rw [show (N : ℝ) * (-1 / N) = -1 by rw [div_eq_mul_one_div, ← mul_assoc, mul_comm (N:ℝ) (-1), mul_assoc, hNN]; ring] at this
      linarith
    rw [max_eq_right hs.le, sub_self, mul_zero, zero_mul, zero_add]
    exact le_max_right _ _
  · push_neg at h1 h2
    have e0 : (N : ℝ) * (-1 / N) + 1 = 0 := by
      rw [div_eq_mul_one_div, ← mul_assoc, mul_comm (N:ℝ) (-1), mul_assoc, hNN]; ring
    rw [e0, max_self, add_zero]
    have ha : 0 ≤ ρ * (c - -1 / N) := mul_nonneg hρ.le (by linarith)
    have hb : ρ * (c - -1 / N) ≤ N := by
      have : c - -1 / N ≤ N / ρ := by linarith
      calc ρ * (c - -1 / N) ≤ ρ * (N / ρ) := mul_le_mul_of_nonneg_left this hρ.le
        _ = N := hρρ
    rcases le_or_gt 0 (t - -1 / N) with ht | ht
    · have : (N : ℝ) * (t - -1 / N) = N * t + 1 := by
        rw [mul_sub, show (N : ℝ) * (-1 / N) = -1 by rw [div_eq_mul_one_div, ← mul_assoc, mul_comm (N:ℝ) (-1), mul_assoc, hNN]; ring]; ring
      calc ρ * (c - -1 / N) * (t - -1 / N) ≤ N * (t - -1 / N) := mul_le_mul_of_nonneg_right hb ht
        _ = N * t + 1 := this
        _ ≤ _ := le_max_left _ _
    · calc ρ * (c - -1 / N) * (t - -1 / N) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha ht.le
        _ ≤ _ := le_max_right _ _

theorem lasso_z_soft_core {N n : ℕ} (hN : 0 < N)
    (x u : Fin N → EuclideanSpace ℝ (Fin n)) (lam ρ : ℝ) (hlam : 0 < lam) (hρ : 0 < ρ)
    (z : EuclideanSpace ℝ (Fin n)) :
    IsMinOn (fun z' : EuclideanSpace ℝ (Fin n) =>
        lam * l1norm z' + (N : ℝ) * ρ / 2 *
          ‖z' - (N : ℝ)⁻¹ • (∑ i, x i) - (N : ℝ)⁻¹ • (∑ i, u i)‖ ^ 2) Set.univ z ↔
      ∀ j, z j = BoydADMM.Prox.softThreshold (lam / (ρ * N))
        (((N : ℝ)⁻¹ • (∑ i, x i)) j + ((N : ℝ)⁻¹ • (∑ i, u i)) j) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set p := (N : ℝ)⁻¹ • (∑ i, x i)
  set q := (N : ℝ)⁻¹ • (∑ i, u i)
  set K := (N : ℝ) * ρ / 2 with hK
  set κ := lam / (ρ * N) with hκ
  have hK0 : 0 < K := by positivity
  have hκ0 : 0 < κ := by positivity
  have hl : lam = 2 * K * κ := by rw [hK, hκ]; field_simp
  let s : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 (fun j => BoydADMM.Prox.softThreshold κ (p j + q j))
  have hs : ∀ j, s j = BoydADMM.Prox.softThreshold κ (p j + q j) := fun j => rfl
  have hf : ∀ y : EuclideanSpace ℝ (Fin n), lam * l1norm y + K * ‖y - p - q‖ ^ 2 =
      (∑ j, (fun t => lam * |t|) (y j)) + K * ‖y - (p + q)‖ ^ 2 := by
    intro y; rw [l1norm, Finset.mul_sum, sub_sub]
  have key := gl_unique_of_growth (fun y : EuclideanSpace ℝ (Fin n) =>
      lam * l1norm y + K * ‖y - p - q‖ ^ 2) s K hK0 (by
    intro y
    simp only [hf]
    refine gl_sep_growth (fun t => lam * |t|) K (p + q) s ?_ y
    intro j t
    simp only [hs, PiLp.add_apply]
    exact gl_soft_1d lam K κ _ t hK0 hκ0 hl) z
  rw [key]
  constructor
  · rintro rfl j; rfl
  · intro h; ext j; rw [h j]

end BoydADMM.ModelFit

open BoydADMM.ModelFit


theorem solution {N n : ℕ} (hN : 0 < N)
    (x u : Fin N → EuclideanSpace ℝ (Fin n)) (lam ρ : ℝ) (hlam : 0 < lam) (hρ : 0 < ρ)
    (z : EuclideanSpace ℝ (Fin n)) :
    IsMinOn (fun z' : EuclideanSpace ℝ (Fin n) =>
        lam * l1norm z' + (N : ℝ) * ρ / 2 *
          ‖z' - (N : ℝ)⁻¹ • (∑ i, x i) - (N : ℝ)⁻¹ • (∑ i, u i)‖ ^ 2) Set.univ z ↔
      ∀ j, z j = BoydADMM.Prox.softThreshold (lam / (ρ * N))
        (((N : ℝ)⁻¹ • (∑ i, x i)) j + ((N : ℝ)⁻¹ • (∑ i, u i)) j) := by
  exact lasso_z_soft_core hN x u lam ρ hlam hρ z

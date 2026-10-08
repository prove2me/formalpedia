-- Prove2me | solution 1 for BoydADMM.ModelFit.group_lasso_block_update
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:03:35.85099+00:00
-- url     : https://prove2.me/submissions/9effcc17-c2a8-4174-9a74-f808956a3932

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

lemma gl_exists_min {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin m))
    (ρ lam : ℝ) (hρ : 0 < ρ) (hlam : 0 < lam) :
    ∃ x, IsMinOn (groupLassoObj ρ lam A v) Set.univ x := by
  have hc : Continuous (groupLassoObj ρ lam A v) := by
    unfold groupLassoObj
    have : Continuous (Matrix.toEuclideanLin A) := LinearMap.continuous_of_finiteDimensional _
    fun_prop
  have ht : Filter.Tendsto (groupLassoObj ρ lam A v) (Filter.cocompact _) Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun x => ?_)
      (Filter.Tendsto.const_mul_atTop hlam tendsto_norm_cocompact_atTop)
    unfold groupLassoObj
    have : 0 ≤ ρ / 2 * ‖Matrix.toEuclideanLin A x - v‖ ^ 2 := by positivity
    linarith
  obtain ⟨x, hx⟩ := hc.exists_forall_le ht
  exact ⟨x, isMinOn_iff.mpr (fun y _ => hx y)⟩

lemma gl_foc {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin m))
    (ρ lam : ℝ) (hρ : 0 < ρ) (hlam : 0 < lam) (x : EuclideanSpace ℝ (Fin n))
    (hx : IsMinOn (groupLassoObj ρ lam A v) Set.univ x) (hx0 : x ≠ 0) :
    Matrix.toEuclideanLin Aᵀ (Matrix.toEuclideanLin A x) + (lam / (ρ * ‖x‖)) • x =
      Matrix.toEuclideanLin Aᵀ v := by
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  set ν := lam / (ρ * ‖x‖) with hν
  have hν0 : 0 < ν := by positivity
  have hl : lam = ρ * ν * ‖x‖ := by rw [hν]; field_simp
  set G := Matrix.toEuclideanLin Aᵀ (Matrix.toEuclideanLin A x) + ν • x -
    Matrix.toEuclideanLin Aᵀ v with hG
  rw [← sub_eq_zero]
  by_contra hG0
  have hnG : 0 < ‖G‖ := norm_pos_iff.mpr hG0
  obtain ⟨t, ht, htB⟩ := gl_small_t (ρ * ‖G‖ ^ 2)
    (ρ / 2 * ‖Matrix.toEuclideanLin A G‖ ^ 2 + ρ * ν / 2 * ‖G‖ ^ 2) (by positivity)
    (by positivity)
  set y := x - t • G with hy
  have hmin := (isMinOn_iff.mp hx) y (Set.mem_univ _)
  have hyx : y - x = -(t • G) := by rw [hy]; abel
  have hgrad : Matrix.toEuclideanLin Aᵀ (Matrix.toEuclideanLin A x - v) = G - ν • x := by
    rw [hG, map_sub]; abel
  have e1 := gl_quad_expand A v x y
  rw [hgrad, hyx, inner_neg_right, inner_smul_right, inner_sub_left, inner_smul_left,
    real_inner_self_eq_norm_sq, map_neg, norm_neg, map_smul, norm_smul,
    Real.norm_of_nonneg ht.le] at e1
  simp only [conj_trivial] at e1
  have e2 := gl_norm_expand x y
  rw [hyx, inner_neg_right, inner_smul_right, norm_neg, norm_smul,
    Real.norm_of_nonneg ht.le] at e2
  have e3 : 2 * ‖x‖ * (‖y‖ - ‖x‖) ≤ ‖y‖ ^ 2 - ‖x‖ ^ 2 := by nlinarith [sq_nonneg (‖y‖ - ‖x‖)]
  have e4 : lam * (‖y‖ - ‖x‖) ≤ ρ * ν / 2 * (‖y‖ ^ 2 - ‖x‖ ^ 2) := by
    rw [hl]
    have := mul_le_mul_of_nonneg_left e3 (by positivity : (0:ℝ) ≤ ρ * ν / 2)
    nlinarith
  unfold groupLassoObj at hmin
  have hin : inner ℝ x G = inner ℝ G x := real_inner_comm _ _
  nlinarith [mul_pos hρ hν0]

theorem group_lasso_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin m)) (ρ lam : ℝ) (hρ : 0 < ρ) (hlam : 0 < lam) :
    (IsMinOn (groupLassoObj ρ lam A v) Set.univ 0 ↔
        ‖Matrix.toEuclideanLin Aᵀ v‖ ≤ lam / ρ) ∧
    (‖Matrix.toEuclideanLin Aᵀ v‖ ≤ lam / ρ →
        ∀ x, IsMinOn (groupLassoObj ρ lam A v) Set.univ x → x = 0) ∧
    (lam / ρ < ‖Matrix.toEuclideanLin Aᵀ v‖ →
        (∃! ν : ℝ, 0 < ν ∧ ν * ‖ridgeSol A ν v‖ = lam / ρ) ∧
        (∀ ν : ℝ, 0 < ν → ν * ‖ridgeSol A ν v‖ = lam / ρ →
          IsMinOn (groupLassoObj ρ lam A v) Set.univ (ridgeSol A ν v)) ∧
        (∀ x, IsMinOn (groupLassoObj ρ lam A v) Set.univ x →
          ∃ ν : ℝ, 0 < ν ∧ ν * ‖x‖ = lam / ρ ∧ x = ridgeSol A ν v)) := by
  set w := Matrix.toEuclideanLin Aᵀ v with hw
  have hdiff : ∀ y, groupLassoObj ρ lam A v y = groupLassoObj ρ lam A v 0 +
      (ρ / 2 * ‖Matrix.toEuclideanLin A y‖ ^ 2 - ρ * inner ℝ y w + lam * ‖y‖) := by
    intro y
    unfold groupLassoObj
    rw [gl_obj_zero_diff A v ρ y, norm_zero, ← hw]
    ring
  have part1 : IsMinOn (groupLassoObj ρ lam A v) Set.univ 0 ↔ ‖w‖ ≤ lam / ρ := by
    rw [isMinOn_iff]
    constructor
    · intro hmin
      by_contra hcon
      push_neg at hcon
      have hwp : 0 < ‖w‖ := lt_trans (by positivity) hcon
      have ha : 0 < ρ * ‖w‖ ^ 2 - lam * ‖w‖ := by
        have : lam < ρ * ‖w‖ := by rwa [div_lt_iff₀ hρ, mul_comm] at hcon
        nlinarith
      obtain ⟨t, ht, htB⟩ := gl_small_t _ (ρ / 2 * ‖Matrix.toEuclideanLin A w‖ ^ 2) ha
        (by positivity)
      have h := hmin (t • w) (Set.mem_univ _)
      rw [hdiff (t • w), map_smul, norm_smul, inner_smul_left, real_inner_self_eq_norm_sq,
        norm_smul, Real.norm_of_nonneg ht.le] at h
      simp only [conj_trivial] at h
      rw [mul_pow] at h
      nlinarith
    · intro hle y _
      rw [hdiff y]
      have h1 : inner ℝ y w ≤ ‖y‖ * ‖w‖ := real_inner_le_norm _ _
      have h2 : ρ * ‖w‖ ≤ lam := by
        have := mul_le_mul_of_nonneg_left hle hρ.le
        rwa [mul_div_cancel₀ _ hρ.ne'] at this
      nlinarith [norm_nonneg y, sq_nonneg ‖Matrix.toEuclideanLin A y‖]
  refine ⟨part1, ?_, ?_⟩
  · intro hle x hx
    have hmin := (isMinOn_iff.mp hx) 0 (Set.mem_univ _)
    rw [hdiff x] at hmin
    have h1 : inner ℝ x w ≤ ‖x‖ * ‖w‖ := real_inner_le_norm _ _
    have h2 : ρ * ‖w‖ ≤ lam := by
      have := mul_le_mul_of_nonneg_left hle hρ.le
      rwa [mul_div_cancel₀ _ hρ.ne'] at this
    have hA : ‖Matrix.toEuclideanLin A x‖ ^ 2 = 0 := by
      nlinarith [norm_nonneg x, sq_nonneg ‖Matrix.toEuclideanLin A x‖]
    have hA' : Matrix.toEuclideanLin A x = 0 := by
      simpa using hA
    have hi : inner ℝ x w = 0 := by
      rw [hw, ← gl_inner_tel, hA', inner_zero_left]
    have : ‖x‖ = 0 := by
      rw [hi] at hmin
      nlinarith [norm_nonneg x, sq_nonneg ‖Matrix.toEuclideanLin A x‖]
    exact norm_eq_zero.mp this
  · intro hlt
    have hnz : ∀ x, IsMinOn (groupLassoObj ρ lam A v) Set.univ x → x ≠ 0 := by
      rintro x hx rfl
      exact absurd (part1.mp hx) (not_le.mpr hlt)
    have char : ∀ x, IsMinOn (groupLassoObj ρ lam A v) Set.univ x →
        ∃ ν : ℝ, 0 < ν ∧ ν * ‖x‖ = lam / ρ ∧ x = ridgeSol A ν v := by
      intro x hx
      have hx0 := hnz x hx
      have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      refine ⟨lam / (ρ * ‖x‖), by positivity, by field_simp, ?_⟩
      exact gl_eq_ridgeSol A _ (by positivity) v x (gl_foc A v ρ lam hρ hlam x hx hx0)
    have suff : ∀ ν : ℝ, 0 < ν → ν * ‖ridgeSol A ν v‖ = lam / ρ →
        IsMinOn (groupLassoObj ρ lam A v) Set.univ (ridgeSol A ν v) := by
      intro ν hν hnorm
      have hl : lam = ρ * ν * ‖ridgeSol A ν v‖ := by
        rw [mul_assoc, hnorm]; field_simp
      rw [isMinOn_iff]
      intro y _
      rw [gl_obj_expand A v ρ lam ν _ (gl_ridgeSol_eq A ν hν v) hl y]
      have h1 : inner ℝ (ridgeSol A ν v) y ≤ ‖ridgeSol A ν v‖ * ‖y‖ := real_inner_le_norm _ _
      have : 0 ≤ ρ * ν * (‖ridgeSol A ν v‖ * ‖y‖ - inner ℝ (ridgeSol A ν v) y) :=
        mul_nonneg (by positivity) (by linarith)
      nlinarith [sq_nonneg ‖Matrix.toEuclideanLin A (y - ridgeSol A ν v)‖]
    refine ⟨?_, suff, char⟩
    obtain ⟨x, hx⟩ := gl_exists_min A v ρ lam hρ hlam
    obtain ⟨ν, hν, hνx, hxr⟩ := char x hx
    refine ⟨ν, ⟨hν, by rw [← hxr]; exact hνx⟩, ?_⟩
    rintro ν2 ⟨hν2, hn2⟩
    -- uniqueness
    set x1 := ridgeSol A ν v with hx1
    set x2 := ridgeSol A ν2 v with hx2
    have hn1 : ν * ‖x1‖ = lam / ρ := by rw [← hxr]; exact hνx
    have hl1 : lam = ρ * ν * ‖x1‖ := by rw [mul_assoc, hn1]; field_simp
    have hl2 : lam = ρ * ν2 * ‖x2‖ := by rw [mul_assoc, hn2]; field_simp
    have q1 := gl_ridgeSol_eq A ν hν v
    have q2 := gl_ridgeSol_eq A ν2 hν2 v
    have E1 := gl_obj_expand A v ρ lam ν x1 q1 hl1 x2
    have E2 := gl_obj_expand A v ρ lam ν2 x2 q2 hl2 x1
    have c1 : inner ℝ x1 x2 ≤ ‖x1‖ * ‖x2‖ := real_inner_le_norm _ _
    have c2 : inner ℝ x2 x1 = inner ℝ x1 x2 := real_inner_comm _ _
    have i1 : 0 ≤ ρ * ν * (‖x1‖ * ‖x2‖ - inner ℝ x1 x2) := mul_nonneg (by positivity) (by linarith)
    have i2 : 0 ≤ ρ * ν2 * (‖x2‖ * ‖x1‖ - inner ℝ x2 x1) :=
      mul_nonneg (by positivity) (by rw [c2]; linarith)
    have hAA : ‖Matrix.toEuclideanLin A (x2 - x1)‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖Matrix.toEuclideanLin A (x2 - x1)‖,
        sq_nonneg ‖Matrix.toEuclideanLin A (x1 - x2)‖]
    have hAx : Matrix.toEuclideanLin A x2 = Matrix.toEuclideanLin A x1 := by
      have : Matrix.toEuclideanLin A (x2 - x1) = 0 := by simpa using hAA
      rw [map_sub, sub_eq_zero] at this
      exact this
    have hsm : ν2 • x2 = ν • x1 := by
      have := q1.trans q2.symm
      rw [hAx] at this
      exact (add_left_cancel this).symm
    by_contra hne
    have hx2' : x2 = (ν / ν2) • x1 := by
      rw [div_eq_inv_mul, ← smul_smul, ← hsm, smul_smul, inv_mul_cancel₀ hν2.ne', one_smul]
    have hA0 : Matrix.toEuclideanLin A x1 = 0 := by
      have h' : (ν / ν2 - 1) • Matrix.toEuclideanLin A x1 = 0 := by
        rw [sub_smul, one_smul, ← map_smul, ← hx2', hAx, sub_self]
      have hc : ν / ν2 - 1 ≠ 0 := by
        intro h0
        apply hne
        have : ν / ν2 = 1 := by linarith
        rw [div_eq_one_iff_eq hν2.ne'] at this
        exact this.symm
      exact (smul_eq_zero.mp h').resolve_left hc
    have : ν • x1 = w := by
      rw [hw, ← q1, hA0, map_zero, zero_add]
    have hnw : ‖w‖ = lam / ρ := by
      rw [← this, norm_smul, Real.norm_of_nonneg hν.le, hn1]
    linarith

end BoydADMM.ModelFit

open BoydADMM.ModelFit


theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin m)) (ρ lam : ℝ) (hρ : 0 < ρ) (hlam : 0 < lam) :
    (IsMinOn (groupLassoObj ρ lam A v) Set.univ 0 ↔
        ‖Matrix.toEuclideanLin Aᵀ v‖ ≤ lam / ρ) ∧
    (‖Matrix.toEuclideanLin Aᵀ v‖ ≤ lam / ρ →
        ∀ x, IsMinOn (groupLassoObj ρ lam A v) Set.univ x → x = 0) ∧
    (lam / ρ < ‖Matrix.toEuclideanLin Aᵀ v‖ →
        (∃! ν : ℝ, 0 < ν ∧ ν * ‖ridgeSol A ν v‖ = lam / ρ) ∧
        (∀ ν : ℝ, 0 < ν → ν * ‖ridgeSol A ν v‖ = lam / ρ →
          IsMinOn (groupLassoObj ρ lam A v) Set.univ (ridgeSol A ν v)) ∧
        (∀ x, IsMinOn (groupLassoObj ρ lam A v) Set.univ x →
          ∃ ν : ℝ, 0 < ν ∧ ν * ‖x‖ = lam / ρ ∧ x = ridgeSol A ν v)) := by
  exact group_lasso_core A v ρ lam hρ hlam

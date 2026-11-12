-- Prove2me | solution 1 for BrouwerLaplacian.proof_lemma_5_5_N
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:14:09.610199+00:00
-- url     : https://prove2.me/submissions/02b5c79d-dbda-42b2-8886-c9e5f74ea143

import Mathlib
import Definitions.Def_BrouwerLaplacian_IsOrthProj
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2
import Definitions.Def_BrouwerLaplacian_centering
import Definitions.Def_BrouwerLaplacian_routingM

section
namespace BrouwerLaplacian.Dev.Common

open Matrix

end BrouwerLaplacian.Dev.Common
end

section
namespace BrouwerLaplacian.Dev.L52

open Finset Matrix

theorem symm_of {n k : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : BrouwerLaplacian.IsOrthProj P k)
    (i j : Fin n) : P j i = P i j := by
  have := hP.1.apply i j
  simpa using this

theorem rowsum {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP1 : P *ᵥ (fun _ => 1) = 0) (i : Fin n) :
    ∑ j, P i j = 0 := by
  have := congrFun hP1 i
  simpa [Matrix.mulVec, dotProduct] using this

end BrouwerLaplacian.Dev.L52

namespace BrouwerLaplacian
open Finset Matrix
end BrouwerLaplacian
end

section
namespace BrouwerLaplacian.Dev.OpN

open Matrix WainwrightHDS.NucNorm

theorem sq_norm_apply {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin N) x‖ ^ 2
      = (N *ᵥ x.ofLp) ⬝ᵥ (N *ᵥ x.ofLp) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [dotProduct, Matrix.toEuclideanLin_apply, sq]

theorem sq_norm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ‖x‖ ^ 2 = x.ofLp ⬝ᵥ x.ofLp := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [dotProduct, sq]

theorem opNorm2_le {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ x : Fin n → ℝ, (N *ᵥ x) ⬝ᵥ (N *ᵥ x) ≤ x ⬝ᵥ x) : opNorm2 N ≤ 1 := by
  unfold opNorm2
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  apply le_of_sq_le_sq _ (norm_nonneg x)
  rw [sq_norm_apply, sq_norm]
  exact h _

theorem opNorm2_ge {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (hx : x ≠ 0)
    (h : (N *ᵥ x) ⬝ᵥ (N *ᵥ x) = x ⬝ᵥ x) : 1 ≤ opNorm2 N := by
  unfold opNorm2
  set f := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin N)
  set y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
  have hy : 0 < ‖y‖ := by
    rw [norm_pos_iff]; intro h0; apply hx; simpa [y] using congrArg WithLp.ofLp h0
  have h1 : ‖f y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [sq_norm_apply, sq_norm]; simpa [y] using h
  have h2 : ‖f y‖ = ‖y‖ := by
    have := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1
    exact this
  have h3 := f.le_opNorm y
  rw [h2] at h3
  by_contra hlt
  push_neg at hlt
  nlinarith

end BrouwerLaplacian.Dev.OpN
end

section
namespace BrouwerLaplacian.Dev.NLem

open Finset Matrix BrouwerLaplacian

theorem cent_apply {n : ℕ} (i j : Fin n) :
    centering n i j = (if i = j then 1 else 0) - (n : ℝ)⁻¹ := by
  simp [centering, onesMat, Matrix.one_apply]

theorem cent_symm {n : ℕ} (i j : Fin n) : centering n j i = centering n i j := by
  rw [cent_apply, cent_apply]; simp [eq_comm]

theorem cent_row {n : ℕ} (i : Fin n) : ∑ j, centering n i j = 0 := by
  simp only [cent_apply, sum_sub_distrib, sum_ite_eq, mem_univ, if_true, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have : (n : ℝ) ≠ 0 := by have := i.pos; positivity
  field_simp; ring

theorem cent_col {n : ℕ} (j : Fin n) : ∑ i, centering n i j = 0 := by
  simp_rw [cent_symm j]; exact cent_row j

theorem cent_mulVec {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    (centering n *ᵥ x) i = x i - (n : ℝ)⁻¹ * ∑ j, x j := by
  simp only [Matrix.mulVec, dotProduct, cent_apply, sub_mul, sum_sub_distrib, ite_mul, one_mul,
    zero_mul, sum_ite_eq, mem_univ, if_true]
  rw [← mul_sum]

theorem cent_mul_cent {n : ℕ} : centering n * centering n = centering n := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [cent_apply, sub_mul, mul_sub, sum_sub_distrib, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    sum_ite_eq, sum_ite_eq', mem_univ, if_true, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (n : ℝ) ≠ 0 := by have := i.pos; positivity
  field_simp; ring

theorem cent_mul_P {n k : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) : centering n * P = P := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [cent_apply, sub_mul, ite_mul, one_mul, zero_mul, sum_sub_distrib, sum_ite_eq, mem_univ,
    if_true, ← mul_sum, ← sum_mul]
  have : ∑ k, P k j = 0 := by
    simp_rw [L52.symm_of hP j]; exact L52.rowsum hP1 j
  rw [this]; simp

theorem P_mul_cent {n k : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) : P * centering n = P := by
  have h := cent_mul_P hP hP1
  have := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul] at this
  have hc : (centering n)ᵀ = centering n := by ext i j; exact cent_symm i j
  have hp : Pᵀ = P := by ext i j; exact L52.symm_of hP i j
  rwa [hc, hp] at this

theorem N_eq {n k : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) : routingN P = centering n - 2 • P := by
  have hCP := cent_mul_P hP hP1
  have hPC := P_mul_cent hP hP1
  have hCC := cent_mul_cent (n := n)
  -- M = A + B - 2P - J + 1
  set d : Fin n → ℝ := fun i => P i i with hd
  have hM : routingM P = (Matrix.of fun i _ => d i) + (Matrix.of fun _ j => d j) - (2 : ℝ) • P
      - onesMat n + 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [routingM, onesMat, d]; ring
    · simp [routingM, onesMat, d, hij]
  have hAC : (Matrix.of fun i _ => d i) * centering n = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, ← mul_sum, Matrix.zero_apply]
    rw [cent_col, mul_zero]
  have hCB : centering n * (Matrix.of fun _ j => d j) = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, ← sum_mul, Matrix.zero_apply]
    rw [cent_row, zero_mul]
  have hJC : onesMat n * centering n = 0 := by
    ext i j
    simp only [Matrix.mul_apply, onesMat, Matrix.of_apply, one_mul, Matrix.zero_apply]
    exact cent_col j
  have hCJ : centering n * onesMat n = 0 := by
    ext i j
    simp only [Matrix.mul_apply, onesMat, Matrix.of_apply, mul_one, Matrix.zero_apply]
    exact cent_row i
  have hCAC : centering n * (Matrix.of fun i _ => d i) * centering n = 0 := by
    rw [Matrix.mul_assoc, hAC, Matrix.mul_zero]
  unfold routingN
  rw [hM]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, hAC, hCB, hJC, hCJ, hCP, hPC, hCC,
    Matrix.zero_mul, Matrix.mul_zero]
  rw [hCAC]; simp only [add_zero, zero_add, sub_zero]
  rw [zero_sub, neg_add_eq_sub]
  rw [(two_smul ℝ P).trans (two_nsmul P).symm]

theorem N_symm {n k : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) : (routingN P)ᵀ = routingN P := by
  rw [N_eq hP hP1]
  have hc : (centering n)ᵀ = centering n := by ext i j; exact cent_symm i j
  have hp : Pᵀ = P := by ext i j; exact L52.symm_of hP i j
  rw [Matrix.transpose_sub, hc, Matrix.transpose_smul, hp]

theorem N_mul_N {n k : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) : routingN P * routingN P = centering n := by
  have hCP := cent_mul_P hP hP1
  have hPC := P_mul_cent hP hP1
  have hCC := cent_mul_cent (n := n)
  have hPP := hP.2.1
  rw [N_eq hP hP1]
  rw [show (2 • P : Matrix (Fin n) (Fin n) ℝ) = P + P from two_nsmul P]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.add_mul, hCP, hPC, hCC, hPP]
  abel

theorem N_mul_P {n k : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) : routingN P * P = -P := by
  have hCP := cent_mul_P hP hP1
  have hPP := hP.2.1
  rw [N_eq hP hP1, show (2 • P : Matrix (Fin n) (Fin n) ℝ) = P + P from two_nsmul P]
  simp only [Matrix.sub_mul, Matrix.add_mul, hCP, hPP]
  abel

theorem cent_one {n : ℕ} : centering n *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  ext i
  rw [cent_mulVec]
  simp
  have : (n : ℝ) ≠ 0 := by have := i.pos; positivity
  field_simp
  norm_num

theorem N_dot {n k : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) (x : Fin n → ℝ) :
    (routingN P *ᵥ x) ⬝ᵥ (routingN P *ᵥ x) = x ⬝ᵥ (centering n *ᵥ x) := by
  have hs := N_symm hP hP1
  have hNN := N_mul_N hP hP1
  rw [Matrix.dotProduct_mulVec]
  conv_lhs => rw [← hs, Matrix.vecMul_transpose, hs, Matrix.mulVec_mulVec, hNN]
  rw [dotProduct_comm]

theorem main {n k : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) :
    routingN P = centering n - 2 • P ∧
    (∀ y : Fin n → ℝ, routingN P *ᵥ (P *ᵥ y) = -(P *ᵥ y)) ∧
    (∀ x : Fin n → ℝ, ∑ i, x i = 0 → P *ᵥ x = 0 → routingN P *ᵥ x = x) ∧
    routingN P *ᵥ (fun _ => 1) = 0 ∧
    WainwrightHDS.NucNorm.opNorm2 (routingN P) ≤ 1 ∧
    (2 ≤ n → WainwrightHDS.NucNorm.opNorm2 (routingN P) = 1) := by
  have hN := N_eq hP hP1
  have hle : WainwrightHDS.NucNorm.opNorm2 (routingN P) ≤ 1 := by
    apply OpN.opNorm2_le
    intro x
    rw [N_dot hP hP1]
    have : x ⬝ᵥ (centering n *ᵥ x) = x ⬝ᵥ x - (n : ℝ)⁻¹ * (∑ i, x i) ^ 2 := by
      simp only [dotProduct, cent_mulVec, mul_sub, sum_sub_distrib]
      rw [← sum_mul]; simp only [sq]; ring
    rw [this]
    have : 0 ≤ (n : ℝ)⁻¹ * (∑ i, x i) ^ 2 := by positivity
    linarith
  refine ⟨hN, ?_, ?_, ?_, hle, ?_⟩
  · intro y
    rw [Matrix.mulVec_mulVec, N_mul_P hP hP1, Matrix.neg_mulVec]
  · intro x hx hPx
    rw [hN, Matrix.sub_mulVec]
    ext i
    have : ((2 • P : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) = 0 := by
      rw [show (2 • P : Matrix (Fin n) (Fin n) ℝ) = P + P from two_nsmul P, Matrix.add_mulVec, hPx]
      simp
    rw [this]
    simp [cent_mulVec, hx]
  · have : ((2 • P : Matrix (Fin n) (Fin n) ℝ) *ᵥ (fun _ => (1:ℝ))) = 0 := by
      rw [show (2 • P : Matrix (Fin n) (Fin n) ℝ) = P + P from two_nsmul P, Matrix.add_mulVec, hP1]
      simp
    rw [hN, Matrix.sub_mulVec, cent_one, this]; simp
  · intro hn
    refine le_antisymm hle ?_
    let i0 : Fin n := ⟨0, by omega⟩
    let i1 : Fin n := ⟨1, by omega⟩
    have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    let x : Fin n → ℝ := Pi.single i0 1 - Pi.single i1 1
    have hsum : ∑ i, x i = 0 := by
      simp [x, Finset.sum_sub_distrib]
    have hx0 : x ≠ 0 := by
      intro h
      have := congrFun h i0
      simp [x, hne] at this
    apply OpN.opNorm2_ge _ x hx0
    rw [N_dot hP hP1]
    simp only [dotProduct, cent_mulVec, mul_sub, sum_sub_distrib, hsum]
    simp

end BrouwerLaplacian.Dev.NLem

namespace BrouwerLaplacian
open Matrix
theorem chk_proof_lemma_5_5_N {n k : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) :
    routingN P = centering n - 2 • P ∧
    (∀ y : Fin n → ℝ, routingN P *ᵥ (P *ᵥ y) = -(P *ᵥ y)) ∧
    (∀ x : Fin n → ℝ, ∑ i, x i = 0 → P *ᵥ x = 0 → routingN P *ᵥ x = x) ∧
    routingN P *ᵥ (fun _ => 1) = 0 ∧
    WainwrightHDS.NucNorm.opNorm2 (routingN P) ≤ 1 ∧
    (2 ≤ n → WainwrightHDS.NucNorm.opNorm2 (routingN P) = 1) := Dev.NLem.main P hP hP1
end BrouwerLaplacian
end

theorem solution : type_of% @BrouwerLaplacian.chk_proof_lemma_5_5_N := @BrouwerLaplacian.chk_proof_lemma_5_5_N

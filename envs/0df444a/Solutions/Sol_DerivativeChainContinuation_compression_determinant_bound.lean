-- Prove2me | solution 1 for DerivativeChainContinuation.compression_determinant_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T18:53:45.326757+00:00
-- url     : https://prove2.me/submissions/3ce267e7-b4a0-4e0a-9b31-d647d4adb45b

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainContinuation_Covariance
import Definitions.Def_DerivativeChainContinuation_MatrixEnergy
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_commutator_energy_le
import Theorems.Thm_DerivativeChainContinuation_compression_deficit_eq
import Theorems.Thm_DerivativeChainContinuation_exists_unitary_triangular
import Theorems.Thm_DerivativeChainContinuation_frobeniusSq_unitary_conjugate
import Theorems.Thm_DerivativeChainContinuation_projection_vectorSq
import Theorems.Thm_DerivativeChainContinuation_rootCompression_commutator_norm
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open scoped BigOperators
open Matrix







theorem centeringProjection_selfAdjoint (n : ℕ) :
    (centeringProjection n).conjTranspose = centeringProjection n := by
  ext i j
  simp [centeringProjection, Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.sub_apply, Matrix.of_apply, eq_comm]





theorem rootCompression_star {n : ℕ} (a : Fin n → ℂ) :
    (rootCompression a).conjTranspose = rootCompression (fun i => star (a i)) := by
  simp only [rootCompression, conjTranspose_mul, diagonal_conjTranspose,
    centeringProjection_selfAdjoint, Function.comp_def]
  rw [Matrix.mul_assoc]
  rfl



end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix Polynomial
open scoped BigOperators

theorem roots_fin_product {n : ℕ} (a : Fin n → ℂ) :
    (∏ i, (X-C (a i))).roots = Finset.univ.val.map a := by
  simpa only [Multiset.map_map, Function.comp_def, Finset.prod_eq_multiset_prod] using
    roots_multiset_prod_X_sub_C (Finset.univ.val.map a)

theorem charpoly_unitary_conjugate {n : ℕ} (M U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ unitaryGroup (Fin n) ℂ) :
    (U.conjTranspose*M*U).charpoly = M.charpoly := by
  have hUU : U*U.conjTranspose = 1 := mem_unitaryGroup_iff.mp hU
  rw [charpoly_mul_comm, ← Matrix.mul_assoc, hUU, one_mul]





end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix
open scoped BigOperators





theorem vectorSq_dot {n : ℕ} (v : Fin n → ℂ) :
    (vectorSq v : ℂ) = star v ⬝ᵥ v := by
  simp [vectorSq, dotProduct, Complex.normSq_eq_conj_mul_self, Complex.star_def]

theorem vectorSq_unitary {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ unitaryGroup (Fin n) ℂ) (v : Fin n → ℂ) :
    vectorSq (U*ᵥv) = vectorSq v := by
  apply Complex.ofReal_injective
  rw [vectorSq_dot, vectorSq_dot, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
  have h : U.conjTranspose*U = 1 := mem_unitaryGroup_iff'.mp hU
  rw [h, one_mulVec]



theorem projection_vectorSq_le {n : ℕ} (hn : n ≠ 0) (v : Fin n → ℂ) :
    vectorSq (centeringProjection n *ᵥ v) ≤ vectorSq v := by
  rw [projection_vectorSq hn]
  exact sub_le_self _ (div_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _))



theorem squareBound_diagonal {n : ℕ} (a : Fin n → ℂ) (r : ℝ)
    (ha : ∀ i, Complex.normSq (a i) ≤ r) : SquareBound (diagonal a) r := by
  intro v
  simp only [vectorSq, Matrix.mulVec_diagonal, map_mul, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (ha i) (Complex.normSq_nonneg _)

theorem squareBound_compression {n : ℕ} (hn : n ≠ 0) (a : Fin n → ℂ)
    (r : ℝ) (hr : 0 ≤ r) (ha : ∀ i, Complex.normSq (a i) ≤ r) :
    SquareBound (rootCompression a) r := by
  intro v
  rw [rootCompression, ← mulVec_mulVec, ← mulVec_mulVec]
  exact (projection_vectorSq_le hn _).trans
    ((squareBound_diagonal a r ha _).trans
      (mul_le_mul_of_nonneg_left (projection_vectorSq_le hn v) hr))

theorem squareBound_unitary {n : ℕ} (M U : Matrix (Fin n) (Fin n) ℂ)
    (r : ℝ) (hM : SquareBound M r) (hU : U ∈ unitaryGroup (Fin n) ℂ) :
    SquareBound (U.conjTranspose*M*U) r := by
  intro v
  have hUs : U.conjTranspose ∈ unitaryGroup (Fin n) ℂ := by
    rw [mem_unitaryGroup_iff']
    simpa only [Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose] using
      (mem_unitaryGroup_iff.mp hU)
  rw [← mulVec_mulVec, ← mulVec_mulVec, vectorSq_unitary _ hUs]
  exact (hM _).trans_eq (by rw [vectorSq_unitary U hU])

end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix Polynomial
open scoped BigOperators





theorem spectral_energy_eq_schur_diagonal {n : ℕ} (B U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ unitaryGroup (Fin n) ℂ)
    (ht : (U.conjTranspose*B*U).IsUpperTriangular) :
    (B.charpoly.roots.map Complex.normSq).sum =
      ∑ i, Complex.normSq ((U.conjTranspose*B*U) i i) := by
  rw [← charpoly_unitary_conjugate B U hU, charpoly_of_isUpperTriangular _ ht,
    roots_fin_product, Multiset.map_map]
  rfl

theorem unitary_commutator {n : ℕ} (B U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ unitaryGroup (Fin n) ℂ) :
    (U.conjTranspose*B*U)*(U.conjTranspose*B*U).conjTranspose -
      (U.conjTranspose*B*U).conjTranspose*(U.conjTranspose*B*U) =
      U.conjTranspose*(B*B.conjTranspose-B.conjTranspose*B)*U := by
  have hUU : U*U.conjTranspose = 1 := mem_unitaryGroup_iff.mp hU
  have he (C D : Matrix (Fin n) (Fin n) ℂ) :
      (U.conjTranspose*C*U)*(U.conjTranspose*D*U) = U.conjTranspose*(C*D)*U := by
    calc
      _ = U.conjTranspose*(C*(U*U.conjTranspose)*D)*U := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hUU, mul_one]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [← Matrix.mul_assoc] at he ⊢
  rw [he, he]
  noncomm_ring



end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution {n : ℕ} (hn : 2 ≤ n)
    (a : Fin n → ℂ) (hc : ∑ i, a i = 0) (R : ℝ)
    (ha : ∀ i, ‖a i‖ ≤ R) :
    (covariance a).det ≤ 2*R^2*schoenbergDeficit (∏ i, (X-C (a i))) := by
  have hn0 : n ≠ 0 := by omega
  have har : ∀ i, Complex.normSq (a i) ≤ R^2 := by
    intro i
    rw [Complex.normSq_eq_norm_sq]
    exact sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (ha i)) |>.mpr (ha i)
  let B := rootCompression a
  obtain ⟨U, hU, ht⟩ := exists_unitary_triangular n B
  let T := U.conjTranspose*B*U
  have hB := squareBound_compression hn0 a (R^2) (sq_nonneg _) har
  have hBs : SquareBound B.conjTranspose (R^2) := by
    rw [rootCompression_star]
    apply squareBound_compression hn0 _ _ (sq_nonneg _)
    intro i
    simpa using har i
  have hT := squareBound_unitary B U _ hB hU
  have hTs : SquareBound T.conjTranspose (R^2) := by
    have h := squareBound_unitary B.conjTranspose U _ hBs hU
    simpa only [T, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc] using h
  have hh := commutator_energy_le T (R^2) hT hTs
  have hcomm : frobeniusSq (T*T.conjTranspose-T.conjTranspose*T) = 8*(covariance a).det := by
    rw [unitary_commutator B U hU, frobeniusSq_unitary_conjugate _ U hU]
    exact rootCompression_commutator_norm hn0 a hc
  have hgap : frobeniusSq T-(∑ i, Complex.normSq (T i i)) =
      schoenbergDeficit (∏ i, (X-C (a i))) := by
    rw [← spectral_energy_eq_schur_diagonal B U hU ht,
      frobeniusSq_unitary_conjugate B U hU, compression_deficit_eq hn a hc]
  rw [hcomm, hgap] at hh
  linarith

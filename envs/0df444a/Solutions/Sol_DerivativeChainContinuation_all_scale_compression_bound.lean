-- Prove2me | solution 1 for DerivativeChainContinuation.all_scale_compression_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:29:14.331202+00:00
-- url     : https://prove2.me/submissions/ef25073b-afd9-456a-975e-23873f9a4016

import Mathlib
import Definitions.Def_DerivativeChainContinuation_AllScaleCompression
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainContinuation_PolynomialMoments
import Definitions.Def_DerivativeChainContinuation_RegularizedGram
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainContinuation_ScaleMoments
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_all_scale_product_exp
import Theorems.Thm_DerivativeChainContinuation_all_scale_product_loss
import Theorems.Thm_DerivativeChainContinuation_compression_deficit_eq
import Theorems.Thm_DerivativeChainContinuation_compression_scale_identity
import Theorems.Thm_DerivativeChainContinuation_diagonal_projection_charpoly
import Theorems.Thm_DerivativeChainContinuation_exists_constant_first_schur
import Theorems.Thm_DerivativeChainContinuation_frobeniusSq_unitary_conjugate
import Theorems.Thm_DerivativeChainContinuation_positive_matrix_hadamard
import Theorems.Thm_DerivativeChainContinuation_regularizedGram_unitary
import Theorems.Thm_DerivativeChainContinuation_scale_gram_factor_bound
import Theorems.Thm_DerivativeChainContinuation_schoenbergDeficit_product_nonneg
import Theorems.Thm_DerivativeChainContinuation_triangular_gram_product_lower
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix Polynomial
open scoped BigOperators ComplexOrder


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial



theorem monicDerivative_monic (p : Polynomial ℂ) (hp : p.Monic)
    (hn : p.natDegree ≠ 0) : (monicDerivative p).Monic := by
  apply monic_C_mul_of_mul_leadingCoeff_eq_one
  rw [leadingCoeff_derivative, hp.leadingCoeff, one_mul]
  exact inv_mul_cancel₀ (by exact_mod_cast hn)








end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open scoped BigOperators
open Matrix









theorem centeringProjection_idempotent {n : ℕ} (hn : n ≠ 0) :
    centeringProjection n * centeringProjection n = centeringProjection n := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  unfold centeringProjection
  simp only [sub_mul, mul_sub, one_mul, mul_one]
  have he : (Matrix.of (fun _ _ : Fin n => (n : ℂ)⁻¹)) * (Matrix.of (fun _ _ : Fin n => (n : ℂ)⁻¹)) =
      (Matrix.of (fun _ _ : Fin n => (n : ℂ)⁻¹)) := by
    ext i j
    simp [Matrix.mul_apply, hnC]
  rw [he]
  abel







end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix Polynomial
open scoped BigOperators



theorem rootCompression_charpoly {n : ℕ} (hn : n ≠ 0) (a : Fin n → ℂ) :
    (rootCompression a).charpoly =
      C (n : ℂ)⁻¹ * X * derivative (∏ i, (X-C (a i))) := by
  rw [rootCompression, charpoly_mul_comm, ← Matrix.mul_assoc,
    centeringProjection_idempotent hn, charpoly_mul_comm,
    diagonal_projection_charpoly hn]

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
open Matrix Polynomial
open scoped BigOperators



theorem compression_charpoly_roots {n : ℕ} (hn : n ≠ 0) (a : Fin n → ℂ) :
    (rootCompression a).charpoly.roots =
      {0} + (monicDerivative (∏ i, (X-C (a i)))).roots := by
  have hd : (∏ i, (X-C (a i))).natDegree = n := by simp
  have hm : (∏ i, (X-C (a i))).Monic := monic_prod_X_sub_C a _
  have hq : (monicDerivative (∏ i, (X-C (a i)))).Monic :=
    monicDerivative_monic _ hm (by rwa [hd])
  have he : (rootCompression a).charpoly = X*monicDerivative (∏ i, (X-C (a i))) := by
    rw [rootCompression_charpoly hn, monicDerivative, hd]
    ring
  rw [he, roots_mul (mul_ne_zero X_ne_zero hq.ne_zero), roots_X]







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





end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix
open scoped BigOperators

theorem constant_unitary_column_sum (n : ℕ)
    (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hQ : Q ∈ unitaryGroup (Fin (n+1)) ℂ)
    (hfirst : ∀ i, Q i 0=((Real.sqrt (n+1:ℝ))⁻¹:ℂ)) (j : Fin n) :
    ∑ i, Q i j.succ=0 := by
  have h := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ => M 0 j.succ)
    (mem_unitaryGroup_iff'.mp hQ)
  have hc : ((Real.sqrt (n+1:ℝ))⁻¹:ℂ) ≠ 0 := by
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by positivity))))
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hfirst, ← Finset.mul_sum] at h
  exact (mul_eq_zero.mp h).resolve_left hc

theorem constant_unitary_projection (n : ℕ)
    (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hQ : Q ∈ unitaryGroup (Fin (n+1)) ℂ)
    (hfirst : ∀ i, Q i 0=((Real.sqrt (n+1:ℝ))⁻¹:ℂ)) :
    centeringProjection (n+1)*Q = Q*diagonal (Fin.cases 0 (fun _ => 1)) := by
  have hn : (n+1:ℂ) ≠ 0 := by exact_mod_cast (show n+1 ≠ 0 by omega)
  ext i j
  rw [centeringProjection, sub_mul, one_mul]
  simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.mul_apply, Matrix.of_apply,
    ← Finset.mul_sum]
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [hfirst, Finset.sum_const, hn, Matrix.diagonal_apply, ← mul_assoc]
  · simp [constant_unitary_column_sum n Q hQ hfirst j, Matrix.diagonal_apply]


end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix
open scoped BigOperators ComplexOrder





theorem regularizedGram_posDef {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (t : ℝ) (ht : 0 < t) : (regularizedGram T t).PosDef := by
  apply Matrix.PosDef.add_posSemidef
  · apply Matrix.PosDef.diagonal
    intro i
    exact_mod_cast ht
  · exact posSemidef_conjTranspose_mul_self T

theorem columnOffDiagonalEnergy_nonneg {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (j : Fin n) : 0 ≤ columnOffDiagonalEnergy T j := by
  unfold columnOffDiagonalEnergy
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact le_refl 0
  · exact Complex.normSq_nonneg _

theorem column_energy_split {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    (∑ i,Complex.normSq (T i j))=Complex.normSq (T j j)+columnOffDiagonalEnergy T j := by
  classical
  have he (i : Fin n) : Complex.normSq (T i j)=
      (if i=j then Complex.normSq (T j j) else 0)+(if i=j then 0 else Complex.normSq (T i j)) := by
    split_ifs with h
    · subst i; simp
    · simp
  calc
    _ = ∑ i, ((if i=j then Complex.normSq (T j j) else 0)+(if i=j then 0 else Complex.normSq (T i j))) :=
      Finset.sum_congr rfl (fun i _ => he i)
    _ = _ := by simp [Finset.sum_add_distrib,columnOffDiagonalEnergy]

theorem total_column_offDiagonal {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) :
    (∑ j,columnOffDiagonalEnergy T j)=frobeniusSq T-∑ j,Complex.normSq (T j j) := by
  have he : frobeniusSq T=(∑ j,Complex.normSq (T j j))+(∑ j,columnOffDiagonalEnergy T j) := by
    rw [frobeniusSq,Finset.sum_comm]
    simp only [column_energy_split,Finset.sum_add_distrib]
  linarith

theorem regularizedGram_diagonal {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) (t : ℝ)
    (j : Fin n) : (regularizedGram T t j j).re=t+Complex.normSq (T j j)+columnOffDiagonalEnergy T j := by
  have he : regularizedGram T t j j=(t:ℂ)+(∑ i,(Complex.normSq (T i j):ℂ)) := by
    simp only [regularizedGram,Matrix.add_apply,Matrix.diagonal_apply,if_pos rfl,ite_true,
      Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.star_def,Complex.normSq_eq_conj_mul_self]
  rw [he]
  simp only [Complex.add_re,Complex.ofReal_re,Complex.re_sum,column_energy_split]
  ring

theorem regularizedGram_hadamard {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (t : ℝ) (ht : 0 < t) :
    ‖(regularizedGram T t).det‖ ≤
      ∏ j,(t+Complex.normSq (T j j)+columnOffDiagonalEnergy T j) := by
  simpa only [regularizedGram_diagonal] using positive_matrix_hadamard _ (regularizedGram_posDef T t ht)
end DerivativeChainContinuation


set_option autoImplicit false
namespace DerivativeChainContinuation
open Matrix
open scoped BigOperators ComplexOrder

theorem gram_determinant_relative_loss {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (t : ℝ) (ht : 0 < t) :
    1-(∏ j,(t+Complex.normSq (T j j)))/‖(regularizedGram T t).det‖ ≤
      min 1 ((frobeniusSq T-∑ j,Complex.normSq (T j j))/t) := by
  have hg : 0 < ‖(regularizedGram T t).det‖ := norm_pos_iff.mpr
    (ne_of_gt (regularizedGram_posDef T t ht).det_pos)
  have h := all_scale_product_loss (fun j => t+Complex.normSq (T j j))
    (columnOffDiagonalEnergy T) t ‖(regularizedGram T t).det‖ ht hg
    (fun j => le_add_of_nonneg_right (Complex.normSq_nonneg _))
    (columnOffDiagonalEnergy_nonneg T) (regularizedGram_hadamard T t ht)
  rwa [total_column_offDiagonal] at h


end DerivativeChainContinuation


set_option autoImplicit false
namespace DerivativeChainContinuation
open Matrix
open scoped BigOperators

theorem scaleMeanZero_complex {n : ℕ} (a : Fin n → ℂ) (t : ℝ) :
    (scaleMeanZero a t:ℂ)=(n:ℂ)⁻¹*(∑ i,((t:ℂ)+(Complex.normSq (a i):ℂ))⁻¹) := by
  simp only [scaleMeanZero,scaleWeight,Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_inv,
    Complex.ofReal_natCast,Complex.ofReal_add]
  simp only [div_eq_mul_inv,← Finset.mul_sum]

theorem scaleMeanOne_complex {n : ℕ} (a : Fin n → ℂ) (t : ℝ) :
    scaleMeanOne a t=(n:ℂ)⁻¹*(∑ i,a i/((t:ℂ)+(Complex.normSq (a i):ℂ))) := by
  simp only [scaleMeanOne,scaleWeight,Complex.ofReal_div,Complex.ofReal_inv,
    Complex.ofReal_natCast,Complex.ofReal_add,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem scaleMeanOne_conjugate {n : ℕ} (a : Fin n → ℂ) (t : ℝ) :
    star (scaleMeanOne a t)=(n:ℂ)⁻¹*(∑ i,star (a i)/((t:ℂ)+(Complex.normSq (a i):ℂ))) := by
  rw [scaleMeanOne_complex]
  simp

theorem compression_scale_real_identity {n : ℕ} (hn : n ≠ 0) (a : Fin n → ℂ)
    (t : ℝ) (ht : 0 < t) :
    (regularizedGram (rootCompression a) t).det =
      ((t*scaleSourceProduct a t*scaleGramFactor a t:ℝ):ℂ) := by
  have hnorm : (Complex.normSq (scaleMeanOne a t):ℂ) =
      ((n:ℂ)⁻¹*(∑ i,star (a i)/((t:ℂ)+(Complex.normSq (a i):ℂ))))*
        ((n:ℂ)⁻¹*(∑ i,a i/((t:ℂ)+(Complex.normSq (a i):ℂ)))) := by
    rw [Complex.normSq_eq_conj_mul_self,← Complex.star_def,scaleMeanOne_conjugate,scaleMeanOne_complex]
  rw [compression_scale_identity hn a t ht]
  simp only [Complex.ofReal_mul,scaleGramFactor,Complex.ofReal_add,Complex.ofReal_pow,
    hnorm,scaleMeanZero_complex,scaleSourceProduct,Complex.ofReal_prod,Complex.ofReal_add]
  ring

theorem scaleSourceProduct_pos {n : ℕ} (a : Fin n → ℂ) (t : ℝ) (ht : 0 < t) :
    0 < scaleSourceProduct a t :=
  Finset.prod_pos fun i _ => add_pos_of_pos_of_nonneg ht (Complex.normSq_nonneg _)

theorem compression_scale_norm_identity {n : ℕ} (hn : n ≠ 0) (a : Fin n → ℂ)
    (t : ℝ) (ht : 0 < t) :
    ‖(regularizedGram (rootCompression a) t).det‖=t*scaleSourceProduct a t*scaleGramFactor a t := by
  rw [compression_scale_real_identity hn a t ht,Complex.norm_real,Real.norm_eq_abs]
  exact abs_of_nonneg (mul_nonneg (mul_nonneg ht.le (scaleSourceProduct_pos a t ht).le)
    (scale_gram_factor_bound hn a t ht).1)
end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix
open scoped BigOperators

theorem rootCompression_shift {n : ℕ} (hn : n ≠ 0) (a : Fin n → ℂ) (z : ℂ) :
    rootCompression (fun i => a i-z)=rootCompression a-z • centeringProjection n := by
  have hd : diagonal (fun i => a i-z)=diagonal a-z • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [smul_one_eq_diagonal]
    ext i j
    simp [Matrix.diagonal_apply,Matrix.sub_apply]
    split_ifs <;> simp
  rw [rootCompression,hd,mul_sub,sub_mul]
  simp only [Matrix.mul_smul,Matrix.smul_mul,mul_one,centeringProjection_idempotent hn,rootCompression]

theorem constant_unitary_projection_diagonal (n : ℕ)
    (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hQ : Q ∈ unitaryGroup (Fin (n+1)) ℂ)
    (hfirst : ∀ i,Q i 0=((Real.sqrt (n+1:ℝ))⁻¹:ℂ)) :
    Q.conjTranspose*centeringProjection (n+1)*Q=diagonal (Fin.cases 0 (fun _ => 1)) := by
  rw [Matrix.mul_assoc,constant_unitary_projection n Q hQ hfirst,← Matrix.mul_assoc]
  have hh : Q.conjTranspose*Q=1 := mem_unitaryGroup_iff'.mp hQ
  rw [hh,one_mul]

theorem pinned_compression_shift (n : ℕ) (a : Fin (n+1) → ℂ) (z : ℂ)
    (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hQ : Q ∈ unitaryGroup (Fin (n+1)) ℂ)
    (hfirst : ∀ i,Q i 0=((Real.sqrt (n+1:ℝ))⁻¹:ℂ)) :
    Q.conjTranspose*rootCompression (fun i => a i-z)*Q =
      Q.conjTranspose*rootCompression a*Q-diagonal (Fin.cases 0 (fun _ => z)) := by
  rw [rootCompression_shift (by omega),mul_sub,sub_mul,Matrix.mul_smul,Matrix.smul_mul,
    constant_unitary_projection_diagonal n Q hQ hfirst]
  congr 1
  rw [← diagonal_smul]
  congr 1
  funext i
  refine Fin.cases ?_ (fun _ => ?_) i <;> simp

theorem columnOffDiagonalEnergy_sub_diagonal {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → ℂ) (j : Fin n) :
    columnOffDiagonalEnergy (T-diagonal d) j=columnOffDiagonalEnergy T j := by
  unfold columnOffDiagonalEnergy
  apply Finset.sum_congr rfl
  intro i _
  by_cases hij : i=j <;> simp [hij,Matrix.sub_apply,Matrix.diagonal_apply]

theorem upperTriangular_sub_diagonal {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.IsUpperTriangular) (d : Fin n → ℂ) : (T-diagonal d).IsUpperTriangular := by
  intro i j hji
  change j < i at hji
  simp [Matrix.sub_apply,Matrix.diagonal_apply,hT hji,ne_of_gt hji]
end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix Polynomial
open scoped BigOperators

theorem det_unitary_conjugate {n : ℕ} (M Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q ∈ unitaryGroup (Fin n) ℂ) : (Q.conjTranspose*M*Q).det=M.det := by
  have hQQ : Q*Q.conjTranspose=1 := mem_unitaryGroup_iff.mp hQ
  rw [det_mul_comm,← Matrix.mul_assoc,hQQ,one_mul]



theorem regularizedGram_det_unitary {n : ℕ} (M Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q ∈ unitaryGroup (Fin n) ℂ) (t : ℝ) :
    (regularizedGram (Q.conjTranspose*M*Q) t).det=(regularizedGram M t).det := by
  rw [regularizedGram_unitary M Q hQ t,det_unitary_conjugate _ Q hQ]

theorem spectral_regularized_product {n : ℕ} (M Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q ∈ unitaryGroup (Fin n) ℂ)
    (htri : (Q.conjTranspose*M*Q).IsUpperTriangular) (t : ℝ) :
    (M.charpoly.roots.map (fun z => t+Complex.normSq z)).prod =
      ∏ j,(t+Complex.normSq ((Q.conjTranspose*M*Q) j j)) := by
  rw [← charpoly_unitary_conjugate M Q hQ,charpoly_of_isUpperTriangular _ htri,
    roots_fin_product,Multiset.map_map]
  rfl
end DerivativeChainContinuation


set_option autoImplicit false
namespace DerivativeChainContinuation
open Matrix
open scoped BigOperators



theorem gram_determinant_exp_bound {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (t : ℝ) (ht : 0 < t) :
    ‖(regularizedGram T t).det‖ ≤ (∏ j,(t+Complex.normSq (T j j)))*
      Real.exp ((frobeniusSq T-∑ j,Complex.normSq (T j j))/t) := by
  have h := all_scale_product_exp (fun j => t+Complex.normSq (T j j))
    (columnOffDiagonalEnergy T) t ‖(regularizedGram T t).det‖ ht
    (fun j => le_add_of_nonneg_right (Complex.normSq_nonneg _))
    (columnOffDiagonalEnergy_nonneg T) (regularizedGram_hadamard T t ht)
  rwa [total_column_offDiagonal] at h
end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace DerivativeChainContinuation
open Matrix Polynomial
open scoped BigOperators ComplexOrder





theorem compression_spectral_product {n : ℕ} (hn : n ≠ 0) (a : Fin n → ℂ) (t : ℝ) :
    ((rootCompression a).charpoly.roots.map (fun b => t+Complex.normSq b)).prod =
      t*scaleDerivativeProduct a t := by
  rw [compression_charpoly_roots hn,Multiset.map_add,Multiset.prod_add,
    Multiset.map_singleton,Multiset.prod_singleton,Complex.normSq_zero,add_zero]
  rfl


end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (n : ℕ) (hn : 0 < n) (a : Fin (n+1) → ℂ)
    (hcenter : ∑ i,a i=0) (z : ℂ) (t : ℝ) (ht : 0 < t) :
    let b := fun i => a i-z;
    let δ := schoenbergDeficit (∏ i,(X-C (a i)));
    0 ≤ scaleCompressionGap b t ∧
      scaleCompressionGap b t ≤ t*scaleMeanZero b t*min 1 (δ/t) ∧
      t*scaleMeanZero b t*min 1 (δ/t) ≤ min 1 (δ/t) ∧
      scaleCompressionGap b t ≤ t*scaleMeanZero b t*(1-Real.exp (-δ/t)) ∧
      (t*scaleMeanZero b t)^2*Real.exp (-δ/t) ≤ t*scaleDerivativeProduct b t/scaleSourceProduct b t := by
  dsimp only
  let b := fun i => a i-z
  let δ := schoenbergDeficit (∏ i,(X-C (a i)))
  let B := rootCompression b
  obtain ⟨Q,hQ,hfirst,htri⟩ := exists_constant_first_schur n a
  let T := Q.conjTranspose*rootCompression a*Q
  let S := Q.conjTranspose*B*Q
  have hshift : S=T-diagonal (Fin.cases 0 (fun _ => z)) := pinned_compression_shift n a z Q hQ hfirst
  have hStri : S.IsUpperTriangular := by
    rw [hshift]
    exact upperTriangular_sub_diagonal T htri _
  have hgap : frobeniusSq S-(∑ j,Complex.normSq (S j j))=δ := by
    rw [← total_column_offDiagonal S,hshift]
    simp only [columnOffDiagonalEnergy_sub_diagonal]
    rw [total_column_offDiagonal,← spectral_energy_eq_schur_diagonal _ Q hQ htri,
      frobeniusSq_unitary_conjugate _ Q hQ]
    exact (compression_deficit_eq (by omega) a hcenter).symm
  have hδ : 0 ≤ δ := schoenbergDeficit_product_nonneg (by omega) a hcenter
  have hmin : 0 ≤ min 1 (δ/t) := le_min (by norm_num) (div_nonneg hδ ht.le)
  have hdet : ‖(regularizedGram S t).det‖=t*scaleSourceProduct b t*scaleGramFactor b t := by
    rw [regularizedGram_det_unitary B Q hQ,compression_scale_norm_identity (by omega) b t ht]
  have hprod : (∏ j,(t+Complex.normSq (S j j)))=t*scaleDerivativeProduct b t := by
    rw [← spectral_regularized_product B Q hQ hStri,compression_spectral_product (by omega)]
  have hG : 0 < t*scaleSourceProduct b t*scaleGramFactor b t := by
    rw [← hdet]
    exact norm_pos_iff.mpr (ne_of_gt (regularizedGram_posDef S t ht).det_pos)
  have hD := scaleSourceProduct_pos b t ht
  have hF : 0 < scaleGramFactor b t := by
    exact (mul_pos_iff_of_pos_left (mul_pos ht hD)).mp hG
  have hrel := gram_determinant_relative_loss S t ht
  rw [hprod,hdet,hgap] at hrel
  have hlower := triangular_gram_product_lower (n+1) S hStri t ht
  rw [hprod,hdet] at hlower
  have hrel0 : 0 ≤ 1-(t*scaleDerivativeProduct b t)/(t*scaleSourceProduct b t*scaleGramFactor b t) := by
    have hh := (div_le_one hG).mpr hlower
    linarith
  have hidentity : scaleCompressionGap b t = t*scaleGramFactor b t*
      (1-(t*scaleDerivativeProduct b t)/(t*scaleSourceProduct b t*scaleGramFactor b t)) := by
    unfold scaleCompressionGap
    field_simp [ht.ne',hD.ne',hF.ne']
    <;> ring
  have hA := scale_gram_factor_bound (by omega) b t ht
  have hexp := gram_determinant_exp_bound S t ht
  rw [hprod,hdet,hgap] at hexp
  have hexp0 : 0 ≤ Real.exp (-δ/t) := (Real.exp_pos _).le
  have hcancel : Real.exp (δ/t)*Real.exp (-δ/t)=1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> congr 1 <;> ring
  have hbeta : t*scaleGramFactor b t*Real.exp (-δ/t) ≤
      t*scaleDerivativeProduct b t/scaleSourceProduct b t := by
    apply (le_div_iff₀ hD).mpr
    have hh := mul_le_mul_of_nonneg_right hexp hexp0
    simp only [mul_assoc,hcancel,mul_one] at hh
    convert hh using 1 <;> ring
  have hone : 0 ≤ 1-Real.exp (-δ/t) := by
    have hh : -δ/t ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ) ht.le
    have he := Real.exp_le_one_iff.mpr hh
    linarith
  have hquadratic : (t*scaleMeanZero b t)^2 ≤ t*scaleGramFactor b t := by
    unfold scaleGramFactor
    nlinarith [mul_nonneg ht.le (Complex.normSq_nonneg (scaleMeanOne b t))]
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [hidentity]
    exact mul_nonneg (mul_nonneg ht.le hF.le) hrel0
  · rw [hidentity]
    exact (mul_le_mul_of_nonneg_left hrel (mul_nonneg ht.le hF.le)).trans
      (mul_le_mul_of_nonneg_right hA.2.1 hmin)
  · exact mul_le_of_le_one_left hmin hA.2.2
  · calc
      scaleCompressionGap b t ≤ t*scaleGramFactor b t*(1-Real.exp (-δ/t)) := by
        unfold scaleCompressionGap
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hA.2.1 hone
  · exact (mul_le_mul_of_nonneg_right hquadratic hexp0).trans hbeta

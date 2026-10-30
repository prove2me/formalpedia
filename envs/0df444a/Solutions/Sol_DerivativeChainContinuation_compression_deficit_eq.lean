-- Prove2me | solution 1 for DerivativeChainContinuation.compression_deficit_eq
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T18:44:03.972834+00:00
-- url     : https://prove2.me/submissions/3c3327cf-0818-4374-a80b-0192db36ab87

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainContinuation_Covariance
import Definitions.Def_DerivativeChainContinuation_PolynomialMoments
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_diagonal_projection_charpoly
import Theorems.Thm_DerivativeChainContinuation_rootCompression_energy
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial



theorem monicDerivative_monic (p : Polynomial ℂ) (hp : p.Monic)
    (hn : p.natDegree ≠ 0) : (monicDerivative p).Monic := by
  apply monic_C_mul_of_mul_leadingCoeff_eq_one
  rw [leadingCoeff_derivative, hp.leadingCoeff, one_mul]
  exact inv_mul_cancel₀ (by exact_mod_cast hn)

theorem monicDerivative_natDegree (p : Polynomial ℂ) (hn : p.natDegree ≠ 0) :
    (monicDerivative p).natDegree = p.natDegree - 1 := by
  rw [monicDerivative, natDegree_C_mul (inv_ne_zero (by exact_mod_cast hn)),
    natDegree_derivative]






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







end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix Polynomial
open scoped BigOperators

theorem product_rootVariance {n : ℕ} (a : Fin n → ℂ) :
    rootVariance (∏ i, (X-C (a i))) = secondMoment a := by
  simp only [rootVariance, roots_fin_product, natDegree_finsetProd_X_sub_C_eq_card,
    Finset.card_univ, Fintype.card_fin, Multiset.map_map, secondMoment]
  rfl

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

open DerivativeChainContinuation in
theorem solution {n : ℕ} (hn : 2 ≤ n)
    (a : Fin n → ℂ) (hc : ∑ i, a i = 0) :
    schoenbergDeficit (∏ i, (X-C (a i))) = frobeniusSq (rootCompression a) -
      ((rootCompression a).charpoly.roots.map Complex.normSq).sum := by
  let p := ∏ i, (X-C (a i))
  have hd : p.natDegree = n := by simp [p]
  have hn0 : n ≠ 0 := by omega
  have hq : (monicDerivative p).natDegree = n-1 := by
    rw [monicDerivative_natDegree _ (by omega), hd]
  have hnR : ((n-1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show n-1 ≠ 0 by omega)
  have hm : ((n-1 : ℕ) : ℝ)*rootVariance (monicDerivative p) =
      ((monicDerivative p).roots.map Complex.normSq).sum := by
    rw [rootVariance, hq]
    field_simp
  change schoenbergDeficit p = _
  rw [schoenbergDeficit, hd, hm, compression_charpoly_roots hn0,
    Multiset.map_add, Multiset.sum_add, Multiset.map_singleton,
    Multiset.sum_singleton, Complex.normSq_zero, zero_add,
    rootCompression_energy hn0 a hc, ← product_rootVariance]
  rw [Nat.cast_sub hn]
  norm_num
  rfl

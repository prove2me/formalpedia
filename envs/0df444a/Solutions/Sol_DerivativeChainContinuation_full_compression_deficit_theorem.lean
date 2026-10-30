-- Prove2me | solution 1 for DerivativeChainContinuation.full_compression_deficit_theorem
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:05:47.136228+00:00
-- url     : https://prove2.me/submissions/e24802f9-b17c-4d78-a85b-695689bc94be

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainContinuation_Covariance
import Definitions.Def_DerivativeChainContinuation_DeficitInequalities
import Definitions.Def_DerivativeChainContinuation_PolynomialMoments
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_compression_deficit_eq
import Theorems.Thm_DerivativeChainContinuation_covariance_moment_formula
import Theorems.Thm_DerivativeChainContinuation_deficit_determinant_inequality
import Theorems.Thm_DerivativeChainContinuation_diagonal_projection_charpoly
import Theorems.Thm_DerivativeChainContinuation_rootCompression_commutator_norm
import Theorems.Thm_DerivativeChainContinuation_rootCompression_energy
import Theorems.Thm_DerivativeChainContinuation_schoenbergDeficit_product_nonneg
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





theorem exists_product_root_slots (p : Polynomial ℂ) (hp : p.Monic) :
    ∃ (n : ℕ) (a : Fin n → ℂ), p = ∏ i, (X-C (a i)) := by
  refine ⟨p.roots.toList.length, p.roots.toList.get, ?_⟩
  have he : Finset.univ.val.map p.roots.toList.get = p.roots := by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
  have hh := congrArg (fun s : Multiset ℂ => (s.map fun z => X-C z).prod) he
  have hh' : (∏ i, (X-C (p.roots.toList.get i))) =
      (p.roots.map fun z => X-C z).prod := by
    simpa only [Multiset.map_map, Function.comp_def, Finset.prod] using hh
  exact ((IsAlgClosed.splits p).eq_prod_roots_of_monic hp).trans hh'.symm



end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix Polynomial
open scoped BigOperators

theorem product_rootCovariance {n : ℕ} (a : Fin n → ℂ) :
    rootCovariance (∏ i, (X-C (a i))) = covariance a := by
  have hh : rootHolomorphicMoment (∏ i, (X-C (a i))) = holomorphicMoment a := by
    simp only [rootHolomorphicMoment, roots_fin_product, natDegree_finsetProd_X_sub_C_eq_card,
      Finset.card_univ, Fintype.card_fin, Multiset.map_map, holomorphicMoment,
      Complex.ofReal_inv, Complex.ofReal_natCast]
    change (∑ i, (a i)^2)/(n : ℂ) = (n : ℂ)⁻¹*(∑ i, (a i)^2)
    ring
  rw [covariance_moment_formula, rootCovariance, product_rootVariance, hh]









end DerivativeChainContinuation

open DerivativeChainContinuation in
/-- Actual compression, energy identity, C3 and C4 for every centered monic source. -/
theorem solution (p : Polynomial ℂ) (hp : p.Monic)
    (hdeg : 2 ≤ p.natDegree) (hc : p.roots.sum = 0) :
    ∃ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℂ), n=p.natDegree ∧
      B.charpoly = X*monicDerivative p ∧
      frobeniusSq B = ((p.natDegree : ℝ)-2)*rootVariance p ∧
      frobeniusSq (B*B.conjTranspose-B.conjTranspose*B) = 8*(rootCovariance p).det ∧
      schoenbergDeficit p = frobeniusSq B-(B.charpoly.roots.map Complex.normSq).sum ∧
      0 ≤ schoenbergDeficit p ∧
      (rootCovariance p).det/(2*(rootRadius p)^2) ≤ schoenbergDeficit p := by
  obtain ⟨n, a, rfl⟩ := exists_product_root_slots p hp
  have hd : (∏ i, (X-C (a i))).natDegree = n := by simp
  have hn : 2 ≤ n := by simpa only [hd] using hdeg
  have hn0 : n ≠ 0 := by omega
  have hca : ∑ i, a i = 0 := by rw [roots_fin_product] at hc; exact hc
  refine ⟨n, rootCompression a, hd.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rootCompression_charpoly hn0, monicDerivative, hd]
    ring
  · rw [hd, product_rootVariance]
    exact rootCompression_energy hn0 a hca
  · rw [product_rootCovariance]
    exact rootCompression_commutator_norm hn0 a hca
  · exact compression_deficit_eq hn a hca
  · exact schoenbergDeficit_product_nonneg hn a hca
  · exact deficit_determinant_inequality _ hp hdeg hc

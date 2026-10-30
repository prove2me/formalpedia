-- Prove2me | solution 1 for DerivativeChainContinuation.deficit_determinant_inequality
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T18:58:01.378629+00:00
-- url     : https://prove2.me/submissions/e3c50087-70d4-4b41-9387-9f808e791bd4

import Mathlib
import Definitions.Def_DerivativeChainContinuation_Covariance
import Definitions.Def_DerivativeChainContinuation_DeficitInequalities
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_compression_determinant_bound
import Theorems.Thm_DerivativeChainContinuation_covariance_moment_formula
import Theorems.Thm_DerivativeChainContinuation_schoenbergDeficit_nonneg
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


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


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators

theorem schoenberg_determinant_bound (p : Polynomial ℂ) (hp : p.Monic)
    (hdeg : 2 ≤ p.natDegree) (hc : p.roots.sum = 0)
    (R : ℝ) (hR : ∀ z ∈ p.roots, ‖z‖ ≤ R) :
    (rootCovariance p).det ≤ 2*R^2*schoenbergDeficit p := by
  obtain ⟨n, a, rfl⟩ := exists_product_root_slots p hp
  have hn : 2 ≤ n := by simpa using hdeg
  have hca : ∑ i, a i = 0 := by rw [roots_fin_product] at hc; exact hc
  have har (i : Fin n) : ‖a i‖ ≤ R := by
    apply hR
    rw [roots_fin_product]
    exact Multiset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
  rw [product_rootCovariance]
  exact compression_determinant_bound hn a hca R har

theorem schoenberg_deficit_ge_determinant (p : Polynomial ℂ) (hp : p.Monic)
    (hdeg : 2 ≤ p.natDegree) (hc : p.roots.sum = 0)
    (R : ℝ) (hR : ∀ z ∈ p.roots, ‖z‖ ≤ R) :
    (rootCovariance p).det/(2*R^2) ≤ schoenbergDeficit p := by
  by_cases hzero : R=0
  · simp only [hzero, zero_pow (by decide : 2 ≠ 0), mul_zero, div_zero]
    exact schoenbergDeficit_nonneg p hp hdeg hc
  · apply (div_le_iff₀ (by positivity : 0 < 2*R^2)).mpr
    nlinarith [schoenberg_determinant_bound p hp hdeg hc R hR]



theorem norm_root_le_rootRadius (p : Polynomial ℂ) (z : ℂ) (hz : z ∈ p.roots) :
    ‖z‖ ≤ rootRadius p := by
  unfold rootRadius
  exact_mod_cast (Finset.le_sup (f := fun z : ℂ => ‖z‖₊) (Multiset.mem_toFinset.mpr hz))





end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (p : Polynomial ℂ) (hp : p.Monic)
    (hdeg : 2 ≤ p.natDegree) (hc : p.roots.sum = 0) :
    (rootCovariance p).det/(2*(rootRadius p)^2) ≤ schoenbergDeficit p :=
  schoenberg_deficit_ge_determinant p hp hdeg hc _ (norm_root_le_rootRadius p)

-- Prove2me | solution 1 for DerivativeChainContinuation.near_collision_cluster_chain
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:05:14.920141+00:00
-- url     : https://prove2.me/submissions/36f077e9-a0f8-4b78-b315-b57734fdecf8

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainContinuation_FiniteNormMean
import Definitions.Def_DerivativeChainContinuation_NearCollisionTower
import Definitions.Def_DerivativeChainContinuation_PolynomialNearCollision
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_complex_tower_factor
import Theorems.Thm_DerivativeChainContinuation_finite_gini_disk_bound
import Theorems.Thm_DerivativeChainContinuation_near_collision_polynomial_chain
import Theorems.Thm_DerivativeChainContinuation_uniform_polynomial_tower
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Polynomial DerivativeChainPrivate
open scoped BigOperators


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
open Polynomial DerivativeChainPrivate
open scoped BigOperators





theorem polynomialGini_C_mul (p : Polynomial ℂ) (c : ℂ) (hc : c ≠ 0) :
    polynomialGini (C c*p)=polynomialGini p := by
  simp only [polynomialGini,roots_C_mul p hc,natDegree_C_mul hc]



theorem polynomialGini_row (r : ComplexRootRows) (k : ℕ) :
    polynomialGini (complexRowProduct r k)=uniformSlotGini r k := by
  simp only [polynomialGini,complexRowProduct,roots_fin_product,
    natDegree_finsetProd_X_sub_C_eq_card,Finset.card_univ,Fintype.card_fin,
    Multiset.map_map,Function.comp_def,Nat.cast_add,Nat.cast_one]
  change (k+1:ℝ)⁻¹*(k+1:ℝ)⁻¹*(∑ i,∑ j,‖r k i-r k j‖)=_
  simp only [uniformSlotGini,finiteGini,← Finset.mul_sum]




end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators

theorem uniform_source_gini_bound (n : ℕ) (a : Fin (n+1) → ℂ)
    (o : ℂ) (R : ℝ) (hR : 0 ≤ R) (ha : ∀ i,‖a i-o‖ ≤ R) :
    polynomialGini (fromRoots a) ≤ Real.sqrt (2*(R^2-‖complexCentroid a-o‖^2)) := by
  let w : Fin (n+1) → ℝ := fun _ => (n+1:ℝ)⁻¹
  have hs : ∑ i,w i=1 := by simp [w,show (n:ℝ)+1 ≠ 0 by positivity]
  have hm : (∑ i,(w i:ℂ)*a i)=complexCentroid a := by
    simp only [w,Complex.ofReal_inv,Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one,
      ← Finset.mul_sum,complexCentroid,div_eq_mul_inv]
    ring
  have hg := finite_gini_disk_bound w a (fun _ => by dsimp [w]; positivity) hs
    (complexCentroid a) o R hR hm ha
  obtain ⟨r,htop,_⟩ := uniform_polynomial_tower n a
  have he := polynomialGini_row r n
  have hg' : uniformSlotGini r n ≤ Real.sqrt (2*(R^2-‖complexCentroid a-o‖^2)) := by
    simpa only [uniformSlotGini,htop,w] using hg
  simpa only [complexRowProduct,htop,fromRoots] using he.trans_le hg'

theorem highest_derivative_gini_zero (n : ℕ) (a : Fin (n+1) → ℂ) :
    polynomialGini (derivative^[n] (fromRoots a))=0 := by
  obtain ⟨r,htop,hstep⟩ := uniform_polynomial_tower n a
  obtain ⟨c,hc,he⟩ := complex_tower_factor r n hstep 0 (by omega)
  have hp : complexRowProduct r n=fromRoots a := by simp only [complexRowProduct,htop,fromRoots]
  rw [hp,Nat.sub_zero] at he
  rw [he,polynomialGini_C_mul _ c hc,polynomialGini_row]
  simp [uniformSlotGini,finiteGini]


end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (n : ℕ) (a : Fin (n+1) → ℂ)
    (ρ : ℕ → ℝ) (K B : ℝ) (hK : 0 < K)
    (hmass : ∀ k<n,∀ x : ℂ,(derivative^[n-k] (fromRoots a)).eval x=0 →
      K⁻¹ ≤ polynomialLocalMass (derivative^[n-k] (fromRoots a)) x (ρ k))
    (hbudget : (∑ k ∈ Finset.range n,ρ k) ≤ B)
    (o : ℂ) (R : ℝ) (hR : 0 ≤ R) (ha : ∀ i,‖a i-o‖ ≤ R) :
    ∃ z : Fin (n+1) → ℂ, DerivativeChainPrivate.IsChain a z ∧
      chainCost z ≤ K*Real.sqrt (2*(R^2-‖complexCentroid a-o‖^2))+2*B := by
  obtain ⟨z,hz,hcost⟩ := near_collision_polynomial_chain n a ρ (fun _ => K⁻¹)
    (fun _ _ => inv_pos.mpr hK) hmass
  have ht (f : ℕ → ℝ) (m : ℕ) : (∑ k ∈ Finset.range m,(f (k+1)-f k))=f m-f 0 := by
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ,ih]; ring
  have he : (∑ k ∈ Finset.range n, (2*ρ k+
        (polynomialGini (derivative^[n-(k+1)] (fromRoots a))-
          polynomialGini (derivative^[n-k] (fromRoots a)))/K⁻¹)) =
      2*(∑ k ∈ Finset.range n,ρ k)+K*polynomialGini (fromRoots a) := by
    simp only [div_inv_eq_mul,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul]
    rw [ht (fun k => polynomialGini (derivative^[n-k] (fromRoots a))) n]
    simp only [Nat.sub_self,Function.iterate_zero_apply,Nat.sub_zero,highest_derivative_gini_zero,sub_zero]
    ring
  rw [he] at hcost
  have hg := mul_le_mul_of_nonneg_left (uniform_source_gini_bound n a o R hR ha) hK.le
  refine ⟨z,hz,?_⟩
  linarith

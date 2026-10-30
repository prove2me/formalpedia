-- Prove2me | solution 1 for DerivativeChainContinuation.near_collision_polynomial_chain
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:01:39.557748+00:00
-- url     : https://prove2.me/submissions/2448e9ce-b580-45a5-8a02-3e501c86472e

import Mathlib
import Definitions.Def_DerivativeChainContinuation_ComplexHistories
import Definitions.Def_DerivativeChainContinuation_NearCollisionTower
import Definitions.Def_DerivativeChainContinuation_PolynomialNearCollision
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_complexRowHistoryCost_attained
import Theorems.Thm_DerivativeChainContinuation_complex_mean_near_collision_step
import Theorems.Thm_DerivativeChainContinuation_complex_tower_factor
import Theorems.Thm_DerivativeChainContinuation_uniform_polynomial_tower
import Theorems.Thm_DerivativeChainPrivate_exists_nonpos_of_probability_mean_zero
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
namespace DerivativeChainContinuation
open scoped BigOperators





theorem finite_weighted_exists_le_mean {ι : Type} [Fintype ι]
    (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i=1) :
    ∃ i, f i ≤ ∑ j, w j*f j := by
  have he : (∑ i, w i*(f i-∑ j, w j*f j))=0 := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hs,one_mul,sub_self]
  obtain ⟨i,hi⟩ := DerivativeChainPrivate.exists_nonpos_of_probability_mean_zero w _ hw hs he
  exact ⟨i,by linarith⟩

end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators











theorem complex_rowHistory_actual (r : ComplexRootRows) (n : ℕ)
    (hstep : ∀ k<n,UniformPolynomialStep r k) (z : Fin (n+1) → ℂ)
    (hz : IsComplexRowHistory r z) :
    ∀ i, (derivative^[n-i.val] (complexRowProduct r n)).eval (z i)=0 := by
  intro i
  obtain ⟨c,hc,heq⟩ := complex_tower_factor r n hstep i.val (by omega)
  obtain ⟨j,hj⟩ := hz i
  rw [heq,eval_mul,eval_C,hj]
  have he : (complexRowProduct r i.val).eval (r i.val j)=0 := by
    simp only [complexRowProduct,eval_prod,eval_sub,eval_X,eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (sub_self _)
  rw [he,mul_zero]
end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators









theorem complex_mean_near_collision_tower (r : ComplexRootRows) (n : ℕ)
    (hstep : ∀ k<n,UniformPolynomialStep r k) (ρ α : ℕ → ℝ)
    (ha : ∀ k<n,0 < α k) (hmass : ∀ k<n,∀ i,α k ≤ rowLocalMass r k (ρ k) i) :
    complexMeanCost r n ≤ ∑ k ∈ Finset.range n,
      (2*ρ k+(uniformSlotGini r (k+1)-uniformSlotGini r k)/α k) := by
  induction n with
  | zero => simp [complexMeanCost,complexRowHistoryCost]
  | succ n ih =>
    have h := complex_mean_near_collision_step r n (hstep n (by omega)) (ρ n) (α n)
      (ha n (by omega)) (hmass n (by omega))
    have hi := ih (fun k hk => hstep k (by omega)) (fun k hk => ha k (by omega))
      (fun k hk => hmass k (by omega))
    rw [Finset.sum_range_succ]
    linarith

theorem near_collision_complete_tower_chain (r : ComplexRootRows) (n : ℕ)
    (hstep : ∀ k<n,UniformPolynomialStep r k) (ρ α : ℕ → ℝ)
    (ha : ∀ k<n,0 < α k) (hmass : ∀ k<n,∀ i,α k ≤ rowLocalMass r k (ρ k) i) :
    ∃ z : Fin (n+1) → ℂ,
      (∀ i,(derivative^[n-i.val] (complexRowProduct r n)).eval (z i)=0) ∧
      chainCost z ≤ ∑ k ∈ Finset.range n,
        (2*ρ k+(uniformSlotGini r (k+1)-uniformSlotGini r k)/α k) := by
  obtain ⟨j,hj⟩ := finite_weighted_exists_le_mean (fun _ : Fin (n+1) => (n+1:ℝ)⁻¹)
    (fun j => complexRowHistoryCost r n (r n j)) (fun _ => by positivity) (by simp [show (n:ℝ)+1 ≠ 0 by positivity])
  obtain ⟨z,hz,_,hc⟩ := complexRowHistoryCost_attained r n (r n j) ⟨j,rfl⟩
  refine ⟨z,complex_rowHistory_actual r n hstep z hz,?_⟩
  rw [hc]
  exact hj.trans (complex_mean_near_collision_tower r n hstep ρ α ha hmass)
end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators





theorem polynomialGini_C_mul (p : Polynomial ℂ) (c : ℂ) (hc : c ≠ 0) :
    polynomialGini (C c*p)=polynomialGini p := by
  simp only [polynomialGini,roots_C_mul p hc,natDegree_C_mul hc]

theorem polynomialLocalMass_C_mul (p : Polynomial ℂ) (c x : ℂ) (hc : c ≠ 0) (ρ : ℝ) :
    polynomialLocalMass (C c*p) x ρ=polynomialLocalMass p x ρ := by
  simp only [polynomialLocalMass,roots_C_mul p hc,natDegree_C_mul hc]

theorem polynomialGini_row (r : ComplexRootRows) (k : ℕ) :
    polynomialGini (complexRowProduct r k)=uniformSlotGini r k := by
  simp only [polynomialGini,complexRowProduct,roots_fin_product,
    natDegree_finsetProd_X_sub_C_eq_card,Finset.card_univ,Fintype.card_fin,
    Multiset.map_map,Function.comp_def,Nat.cast_add,Nat.cast_one]
  change (k+1:ℝ)⁻¹*(k+1:ℝ)⁻¹*(∑ i,∑ j,‖r k i-r k j‖)=_
  simp only [uniformSlotGini,finiteGini,← Finset.mul_sum]

theorem polynomialLocalMass_row (r : ComplexRootRows) (k : ℕ) (ρ : ℝ) (i : Fin (k+1)) :
    polynomialLocalMass (complexRowProduct r k) (r k i) ρ=rowLocalMass r k ρ i := by
  classical
  simp only [polynomialLocalMass,complexRowProduct,roots_fin_product,
    natDegree_finsetProd_X_sub_C_eq_card,Finset.card_univ,Fintype.card_fin,
    Multiset.map_map,Function.comp_def,Nat.cast_add,Nat.cast_one]
  change (k+1:ℝ)⁻¹*(∑ j, if ‖r k i-r k j‖ ≤ ρ then (1:ℝ) else 0)=_
  simp only [Finset.mul_sum,mul_ite,mul_one,mul_zero,rowLocalMass]


end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (n : ℕ) (a : Fin (n+1) → ℂ) (ρ α : ℕ → ℝ)
    (ha : ∀ k<n, 0 < α k)
    (hmass : ∀ k<n,∀ x : ℂ,(derivative^[n-k] (fromRoots a)).eval x=0 →
      α k ≤ polynomialLocalMass (derivative^[n-k] (fromRoots a)) x (ρ k)) :
    ∃ z : Fin (n+1) → ℂ, DerivativeChainPrivate.IsChain a z ∧
      chainCost z ≤ ∑ k ∈ Finset.range n, (2*ρ k+
        (polynomialGini (derivative^[n-(k+1)] (fromRoots a))-
          polynomialGini (derivative^[n-k] (fromRoots a)))/α k) := by
  obtain ⟨r,htop,hstep⟩ := uniform_polynomial_tower n a
  have hp : complexRowProduct r n=fromRoots a := by simp only [complexRowProduct,htop,fromRoots]
  have hg (k : ℕ) (hk : k≤n) : polynomialGini (derivative^[n-k] (fromRoots a))=uniformSlotGini r k := by
    obtain ⟨c,hc,he⟩ := complex_tower_factor r n hstep k hk
    rw [hp] at he
    rw [he,polynomialGini_C_mul _ c hc,polynomialGini_row]
  have hm (k : ℕ) (hk : k<n) (i : Fin (k+1)) : α k ≤ rowLocalMass r k (ρ k) i := by
    obtain ⟨c,hc,he⟩ := complex_tower_factor r n hstep k hk.le
    rw [hp] at he
    have hr : (complexRowProduct r k).eval (r k i)=0 := by
      simp only [complexRowProduct,eval_prod,eval_sub,eval_X,eval_C]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
    have hx : (derivative^[n-k] (fromRoots a)).eval (r k i)=0 := by rw [he,eval_mul,hr,mul_zero]
    have hh := hmass k hk (r k i) hx
    rwa [he,polynomialLocalMass_C_mul _ c _ hc,polynomialLocalMass_row] at hh
  obtain ⟨z,hz,hc⟩ := near_collision_complete_tower_chain r n hstep ρ α ha hm
  refine ⟨z,?_,?_⟩
  · intro i
    have he : n+1-(i.val+1)=n-i.val := by omega
    simpa only [DerivativeChainPrivate.IsChain,row,he,hp] using hz i
  · convert hc using 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [hg k (by have := Finset.mem_range.mp hk; omega),hg (k+1) (by have := Finset.mem_range.mp hk; omega)]

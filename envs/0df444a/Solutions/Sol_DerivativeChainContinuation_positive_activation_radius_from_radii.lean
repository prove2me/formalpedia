-- Prove2me | solution 1 for DerivativeChainContinuation.positive_activation_radius_from_radii
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:25:00.56911+00:00
-- url     : https://prove2.me/submissions/9f5908e6-090a-4d25-aab3-163243d1ea92

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveGreedyChain
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_positive_activation_radius
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators



theorem realRootProduct_monic {n : ℕ} (a : Fin n → ℝ) :
    (realRootProduct a).Monic := Polynomial.monic_prod_X_sub_C a Finset.univ

theorem realRootProduct_degree {n : ℕ} (a : Fin n → ℝ) :
    (realRootProduct a).natDegree = n := by
  unfold realRootProduct
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (a i))]
  simp






end DerivativeChainContinuation


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators

theorem realRootProduct_roots {n : ℕ} (a : Fin n → ℝ) :
    (realRootProduct a).roots = Finset.univ.val.map a := by
  have hprod : realRootProduct a =
      ((Finset.univ.val.map a).map fun x => (X-C x : Polynomial ℝ)).prod := by
    simp only [Multiset.map_map,Function.comp_def]
    rfl
  rw [hprod,roots_multiset_prod_X_sub_C]

theorem realRootProduct_splits {n : ℕ} (a : Fin n → ℝ) :
    (realRootProduct a).Splits := by
  apply splits_iff_card_roots.mpr
  simp [realRootProduct_roots,realRootProduct_degree]











end DerivativeChainContinuation

theorem solution (n d : ℕ) (a z : Fin (n+1) → ℂ)
    (k r : ℕ) (ρ : Fin (d+1) → ℝ) (hk : 2 ≤ k) (hρ : ∀ j,0<ρ j)
    (hp : fromRoots a=spokePoly k r (realRootProduct (fun j => (ρ j)^k)))
    (hz : DerivativeChainPrivate.IsChain a z) :
    ‖complexHistoryOf z (k-1)‖=((∑ j,(ρ j)^k)/(Nat.choose (n+1) k : ℝ))^((k : ℝ)⁻¹) := by
  let Q := realRootProduct (fun j => (ρ j)^k)
  have hQ : PositiveQuotient Q := by
    refine ⟨(realRootProduct_monic _).ne_zero,realRootProduct_splits _,?_⟩
    intro y hy
    rw [realRootProduct_roots] at hy
    obtain ⟨j,_,rfl⟩ := Multiset.mem_map.mp hy
    exact pow_pos (hρ j) k
  have hQdegree : 0<Q.natDegree := by rw [realRootProduct_degree]; omega
  have hsum : Q.roots.sum=∑ j,(ρ j)^k := by
    simp only [Q,realRootProduct_roots,Finset.sum_map_val]
  have h := positive_activation_radius n a z k r Q hk hQ hQdegree hp hz
  rwa [hsum] at h

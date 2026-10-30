-- Prove2me | solution 1 for DerivativeChainContinuation.actual_real_row_root_iff
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:36:18.358982+00:00
-- url     : https://prove2.me/submissions/569d2765-e75a-4eb6-b040-97c56091616a

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_real_tower_factor
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators



theorem real_source_map {n : ℕ} (a : Fin (n+1) → ℝ) :
    fromRoots (fun i => (a i : ℂ))=(realRootProduct a).map Complex.ofRealHom := by
  simp only [fromRoots,realRootProduct,Polynomial.map_prod,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,Complex.ofRealHom_eq_coe]





















end DerivativeChainContinuation

theorem solution (r : RealRows) (n : ℕ)
    (hstep : ∀ k<n,RealRowStep r k) (k : ℕ) (hk : k≤n) (w : ℂ) :
    (row (fun i => (r n i : ℂ)) (k+1)).eval w=0 ↔
      ∃ j : Fin (k+1), w=(r k j : ℂ) := by
  obtain ⟨c,hc,heq⟩ := real_tower_factor r n hstep k hk
  have hr : row (fun i => (r n i : ℂ)) (k+1)=
      (C c*realRootProduct (r k)).map Complex.ofRealHom := by
    unfold row
    rw [real_source_map,iterate_derivative_map]
    rw [show n+1-(k+1)=n-k by omega,heq]
  rw [hr]
  simp only [Polynomial.map_mul,map_C,realRootProduct,Polynomial.map_prod,
    Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,Complex.ofRealHom_eq_coe,eval_mul,eval_C,eval_prod,eval_sub,eval_X]
  have hc' : (c : ℂ)≠0 := by exact_mod_cast hc
  rw [mul_eq_zero,or_iff_right hc',Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ,true_and,sub_eq_zero]

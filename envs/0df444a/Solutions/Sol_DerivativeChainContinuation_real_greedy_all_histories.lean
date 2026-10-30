-- Prove2me | solution 1 for DerivativeChainContinuation.real_greedy_all_histories
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:57:06.939962+00:00
-- url     : https://prove2.me/submissions/48f6c59f-e317-4d50-8953-f60d4d20586d

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyActual
import Definitions.Def_DerivativeChainContinuation_GreedyReal
import Definitions.Def_DerivativeChainContinuation_GreedyStatement
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainContinuation_RealTransportGeneral
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_actual_real_greedy_classification
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


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators



theorem realRootProduct_reindex {n : ℕ} (a : Fin n → ℝ) (e : Equiv.Perm (Fin n)) :
    realRootProduct (a ∘ e)=realRootProduct a := by
  exact Equiv.prod_comp e (fun i => X-C (a i))










end DerivativeChainContinuation


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators



theorem orderedSource_mono {n : ℕ} (a : Fin (n+1) → ℝ) : Monotone (orderedSource a) :=
  Tuple.monotone_sort a



theorem orderedSource_fromRoots {n : ℕ} (a : Fin (n+1) → ℝ) :
    fromRoots (fun i => (a i : ℂ))=
      fromRoots (fun i => (orderedSource a i : ℂ)) := by
  rw [real_source_map,real_source_map]
  unfold orderedSource
  rw [realRootProduct_reindex]

theorem orderedSource_greedy_iff {n : ℕ} (a : Fin (n+1) → ℝ)
    (z : Fin (n+1) → ℂ) :
    IsGreedyChain (fun i => (a i : ℂ)) z ↔
      IsGreedyChain (fun i => (orderedSource a i : ℂ)) z := by
  simp only [IsGreedyChain,DerivativeChainPrivate.IsChain,row,orderedSource_fromRoots a]

theorem orderedSource_centroid {n : ℕ} (a : Fin (n+1) → ℝ) :
    realCentroid (orderedSource a)=realCentroid a := by
  unfold realCentroid orderedSource
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp (Tuple.sort a) a]













end DerivativeChainContinuation

theorem solution (n : ℕ) (hn : 1≤n) (a : Fin (n+1) → ℝ) :
    ∃ r : RealRows, r n=orderedSource a ∧
      (∀ k≤n,Monotone (r k)) ∧ (∀ k<n,RealRowStep r k) ∧
      (∀ k≤n,∀ w : ℂ,
        (row (fun i => (a i : ℂ)) (k+1)).eval w=0 ↔
          ∃ j : Fin (k+1),w=(r k j : ℂ)) ∧
      (∀ z : Fin (n+1) → ℂ, IsGreedyChain (fun i => (a i : ℂ)) z ↔
        (∀ i,z i=(leftRow r i.val : ℂ)) ∨
        (∀ i,z i=(rightRow r i.val : ℂ))) ∧
      (∀ z : Fin (n+1) → ℂ, IsGreedyChain (fun i => (a i : ℂ)) z →
        chainCost z=realCentroid a-orderedSource a 0 ∨
        chainCost z=orderedSource a (Fin.last n)-realCentroid a) ∧
      (∃ z : Fin (n+1) → ℂ, IsGreedyChain (fun i => (a i : ℂ)) z ∧
        chainCost z≤(orderedSource a (Fin.last n)-orderedSource a 0)/2) := by
  obtain ⟨r,hr,hm,hs,hrows,hclass,hcost,hex⟩ :=
    actual_real_greedy_classification n hn (orderedSource a) (orderedSource_mono a)
  refine ⟨r,hr,hm,hs,?_,?_,?_,?_⟩
  · intro k hk w
    simpa only [row,←orderedSource_fromRoots a] using hrows k hk w
  · intro z
    exact (orderedSource_greedy_iff a z).trans (hclass z)
  · intro z hz
    have h := hcost z ((orderedSource_greedy_iff a z).mp hz)
    simpa only [orderedSource_centroid] using h
  · obtain ⟨z,hz,hc⟩ := hex
    exact ⟨z,(orderedSource_greedy_iff a z).mpr hz,hc⟩

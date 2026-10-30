-- Prove2me | solution 1 for DerivativeChainContinuation.real_transport_chain_family
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T17:43:37.533955+00:00
-- url     : https://prove2.me/submissions/793f89af-cc5f-49dc-a6ed-c0d76b276607

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RealHistories
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainContinuation_RealTransportBound
import Definitions.Def_DerivativeChainContinuation_RealTransportGeneral
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_centered_ordered_transport
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators



theorem realRootProduct_reindex {n : ℕ} (a : Fin n → ℝ) (e : Equiv.Perm (Fin n)) :
    realRootProduct (a ∘ e)=realRootProduct a := by
  exact Equiv.prod_comp e (fun i => X-C (a i))

theorem realRootProduct_translate {n : ℕ} (a : Fin n → ℝ) (u : ℝ) :
    realRootProduct (fun i => a i-u)=(realRootProduct a).comp (X+C u) := by
  simp only [realRootProduct,Polynomial.prod_comp,sub_comp,X_comp,C_comp]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_sub]
  ring

theorem iterate_derivative_translate {R : Type*} [CommRing R] (p : Polynomial R) (u : R) (k : ℕ) :
    (derivative^[k] (p.comp (X+C u)))=(derivative^[k] p).comp (X+C u) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',ih,derivative_comp]
    simp

theorem realChainCost_translate {n : ℕ} (z : Fin (n+1) → ℝ) (u : ℝ) :
    realChainCost (fun i => z i+u)=realChainCost z := by
  simp only [realChainCost,add_sub_add_right_eq_sub]




end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (n : ℕ) (hn : 0<n) (a : Fin (n+1) → ℝ) :
    ∃ z : Fin (n+1) → Fin (n+1) → ℝ,
      (∀ j,IsRealDerivativeChain (realRootProduct a) n (z j)) ∧
      (∀ j,z j (Fin.last n)=a j) ∧
      (∑ j,(realChainCost (z j))^2) ≤
        (28/3 : ℝ)*(∑ i,(a i-realCentroid a)^2) := by
  classical
  let e := Tuple.sort a
  let u := realCentroid a
  let b : Fin (n+1) → ℝ := fun i => a (e i)-u
  have hmono : Monotone b := by
    intro i j hij
    have h := Tuple.monotone_sort a hij
    exact sub_le_sub_right h u
  have hcenter : ∑ i,b i=0 := by
    dsimp [b]
    rw [Finset.sum_sub_distrib,Equiv.sum_comp e a]
    simp [u,realCentroid]
    field_simp
    ring
  have hpoly : realRootProduct b=(realRootProduct a).comp (X+C u) := by
    rw [show b=(fun i => (a ∘ e) i-u) from rfl,realRootProduct_translate,realRootProduct_reindex]
  obtain ⟨z,hz,he,hcost⟩ := centered_ordered_transport n hn b hmono hcenter
  let zz : Fin (n+1) → Fin (n+1) → ℝ := fun j i => z (e.symm j) i+u
  refine ⟨zz,?_,?_,?_⟩
  · intro j i
    have h := hz (e.symm j) i
    rw [hpoly,iterate_derivative_translate,eval_comp] at h
    simpa [zz] using h
  · intro j
    simp [zz,he,b]
  · have hc : ∑ j,(realChainCost (zz j))^2 = ∑ j,(realChainCost (z j))^2 := by
      simp only [zz,realChainCost_translate]
      exact Equiv.sum_comp e.symm (fun j => (realChainCost (z j))^2)
    have hv : ∑ i,(b i)^2 = ∑ i,(a i-u)^2 := Equiv.sum_comp e (fun i => (a i-u)^2)
    rw [hc]
    simpa only [hv] using hcost

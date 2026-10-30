-- Prove2me | solution 1 for DerivativeChainClusterAnchor.majority_atom
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T06:00:54.320801+00:00
-- url     : https://prove2.me/submissions/4ff71607-07f2-4910-a323-35e977191499

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainClusterAnchor_actual_polynomial_slots
import Theorems.Thm_DerivativeChainClusterAnchor_majority_atom_array
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate


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
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation DerivativeChainPrivate
open DerivativeChainClusterAnchor








theorem solution (p : ℂ[X]) (hp : p.Monic) (n r : ℕ) (hdegree : p.natDegree=n)
    (hcube : r^3 ≤ n^2) (o c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hsource : ∀ z ∈ p.roots, ‖z-o‖ ≤ R) (hc : c ∈ p.roots)
    (hmultiplicity : n-r ≤ p.roots.count c) :
    ∃ z : Fin n → ℂ, (∀ i, (derivative^[n-(i.val+1)] p).eval (z i)=0) ∧
      _root_.DerivativeChainPrivate.chainCost z ≤ (2+Real.sqrt 2)*R := by
  classical
  have hcardroots : p.roots.card=n := (IsAlgClosed.splits p).natDegree_eq_card_roots.symm.trans hdegree
  have hn : 0 < n := by
    rw [← hcardroots]
    exact Multiset.card_pos_iff_exists_mem.mpr ⟨c,hc⟩
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨a,hpa,hmem,hcard⟩ := _root_.DerivativeChainClusterAnchor.actual_polynomial_slots p hp (n+1) hdegree (fun z => z ≠ c)
    have hpart := congrArg Multiset.card (Multiset.filter_add_not (fun z : ℂ => z ≠ c) p.roots)
    simp only [Multiset.card_add,not_not,Multiset.filter_eq',Multiset.card_replicate,hcardroots] at hpart
    have hbad : (p.roots.filter (fun z => z ≠ c)).card ≤ r := by omega
    let O := (Finset.univ : Finset (Fin (n+1))).filter (fun i => a i ≠ c)
    have hO : O.card ≤ r := hcard.le.trans hbad
    have hnear (i : Fin (n+1)) (hi : i ∉ O) : a i=c := by simpa [O] using hi
    have hcarray : ∃ i, a i=c := by
      have hcmem := hc
      rw [hpa,_root_.DerivativeChainPrivate.fromRoots,_root_.DerivativeChainContinuation.roots_fin_product] at hcmem
      obtain ⟨i,_,hi⟩ := Multiset.mem_map.mp hcmem
      exact ⟨i,hi⟩
    obtain ⟨z,hz,hcost⟩ := _root_.DerivativeChainClusterAnchor.majority_atom_array n r a o c O R hcube hO hR
      (fun i => hsource (a i) (hmem i)) hcarray hnear
    refine ⟨z,?_,hcost⟩
    intro i
    rw [hpa]
    exact hz i

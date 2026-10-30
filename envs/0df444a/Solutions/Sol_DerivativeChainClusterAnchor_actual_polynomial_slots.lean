-- Prove2me | solution 1 for DerivativeChainClusterAnchor.actual_polynomial_slots
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T05:29:59.55252+00:00
-- url     : https://prove2.me/submissions/24cd18e8-2ade-426c-959b-21f9458de5a1

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
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
namespace DerivativeChainContinuation
open Matrix Polynomial
open scoped BigOperators







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
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation DerivativeChainPrivate
open DerivativeChainClusterAnchor


theorem solution (p : ℂ[X]) (hp : p.Monic) (n : ℕ) (hdegree : p.natDegree=n)
    (f : ℂ → Prop) [DecidablePred f] :
    ∃ a : Fin n → ℂ, p=_root_.DerivativeChainPrivate.fromRoots a ∧ (∀ i, a i ∈ p.roots) ∧
      ((Finset.univ : Finset (Fin n)).filter (fun i => f (a i))).card=(p.roots.filter f).card := by
  classical
  obtain ⟨m,a,hprod⟩ := _root_.DerivativeChainContinuation.exists_product_root_slots p hp
  have hm : m=n := by
    have hd := congrArg Polynomial.natDegree hprod
    simpa only [hdegree,natDegree_finsetProd_X_sub_C_eq_card,Finset.card_univ,Fintype.card_fin] using hd.symm
  subst m
  have hpa : p=_root_.DerivativeChainPrivate.fromRoots a := by simpa only [_root_.DerivativeChainPrivate.fromRoots] using hprod
  refine ⟨a,hpa,?_,?_⟩
  · intro i
    rw [hpa,_root_.DerivativeChainPrivate.fromRoots,_root_.DerivativeChainContinuation.roots_fin_product]
    exact Multiset.mem_map.mpr ⟨i,by simp,rfl⟩
  · rw [hpa,_root_.DerivativeChainPrivate.fromRoots,_root_.DerivativeChainContinuation.roots_fin_product,Multiset.filter_map,Multiset.card_map]
    rfl

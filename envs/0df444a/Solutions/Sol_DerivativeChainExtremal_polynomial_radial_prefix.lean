-- Prove2me | solution 1 for DerivativeChainExtremal.polynomial_radial_prefix
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:10:07.518962+00:00
-- url     : https://prove2.me/submissions/feb1ccb3-b3ca-433e-817f-8c42abc1bcfd

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CenteredSource
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainExtremal_mixed_sign_radial_prefix_arbitrary_suffix
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainExtremal
end DerivativeChainExtremal
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
set_option maxHeartbeats 2000000
namespace DerivativeChainExtremal
open Polynomial DerivativeChainPrivate DerivativeChainContinuation
open scoped BigOperators

theorem rootCentroid_fromRoots {n : ℕ} (a : Fin (n+1) → ℂ) :
    rootCentroid (fromRoots a)=complexCentroid a := by
  simp only [rootCentroid,fromRoots,roots_fin_product,natDegree_finsetProd_X_sub_C_eq_card,
    Finset.card_univ,Fintype.card_fin,complexCentroid,Finset.sum_map_val,Nat.cast_add,Nat.cast_one]

theorem monic_polynomial_radial_prefix (p : Polynomial ℂ) (hp : p.Monic)
    (n m k r : ℕ) (hdegree : p.natDegree=n+1) (q : Polynomial ℝ) (σ C₀ o : ℂ) (R : ℝ)
    (hm : 1 ≤ m) (hmn : m ≤ n+1) (hk : 2 ≤ k) (hr : r < k)
    (hq : q.Splits) (hC : C₀ ≠ 0) (hσ : ‖σ‖=1)
    (hcore : (derivative^[n+1-m] p).comp (C (rootCentroid p)+C σ*X)=C C₀*spokePoly k r q)
    (hR : 0 ≤ R) (ha : ∀ w : ℂ, p.eval w=0 → ‖w-o‖ ≤ R) :
    ∃ z : Fin (n+1) → ℂ,
      (∀ i, (derivative^[n+1-(i.val+1)] p).eval (z i)=0) ∧ z 0=rootCentroid p ∧
      chainCost z ≤ Real.sqrt (n+1-m+1 : ℕ)*Real.sqrt (R^2-‖rootCentroid p-o‖^2) := by
  obtain ⟨N,a,hprod⟩ := exists_product_root_slots p hp
  have hN : N=n+1 := by
    have h := congrArg natDegree hprod
    simpa only [hdegree,natDegree_finsetProd_X_sub_C_eq_card,Finset.card_univ,Fintype.card_fin] using h.symm
  subst N
  have hfrom : fromRoots a=p := hprod.symm
  have hcentroid : complexCentroid a=rootCentroid p := by rw [←hfrom,rootCentroid_fromRoots]
  have hcore' : (row a m).comp (C (complexCentroid a)+C σ*X)=C C₀*spokePoly k r q := by
    simpa only [row,hfrom,hcentroid] using hcore
  have ha' (i : Fin (n+1)) : ‖a i-o‖ ≤ R := by
    apply ha
    rw [←hfrom]
    simp only [fromRoots,eval_prod,eval_sub,eval_X,eval_C]
    exact Finset.prod_eq_zero_iff.mpr ⟨i,Finset.mem_univ i,sub_self _⟩
  obtain ⟨z,hz,hz0,hcost⟩ := mixed_sign_radial_prefix_arbitrary_suffix a m k r q σ C₀ o R
    hm hmn hk hr hq hC hσ hcore' hR ha'
  refine ⟨z,?_,?_,?_⟩
  · intro i
    simpa only [DerivativeChainPrivate.IsChain,row,hfrom] using hz i
  · simpa only [hcentroid] using hz0
  · simpa only [hcentroid] using hcost






end DerivativeChainExtremal


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open DerivativeChainExtremal
open Polynomial DerivativeChainPrivate DerivativeChainContinuation
open scoped BigOperators





theorem solution (p : Polynomial ℂ)
    (n m k r : ℕ) (hdegree : p.natDegree=n+1) (q : Polynomial ℝ) (σ C₀ o : ℂ) (R : ℝ)
    (hm : 1 ≤ m) (hmn : m ≤ n+1) (hk : 2 ≤ k) (hr : r < k)
    (hq : q.Splits) (hC : C₀ ≠ 0) (hσ : ‖σ‖=1)
    (hcore : (derivative^[n+1-m] p).comp (C (_root_.DerivativeChainContinuation.rootCentroid p)+C σ*X)=C C₀*_root_.DerivativeChainPrivate.spokePoly k r q)
    (hR : 0 ≤ R) (ha : ∀ w : ℂ, p.eval w=0 → ‖w-o‖ ≤ R) :
    ∃ z : Fin (n+1) → ℂ,
      (∀ i, (derivative^[n+1-(i.val+1)] p).eval (z i)=0) ∧ z 0=_root_.DerivativeChainContinuation.rootCentroid p ∧
      _root_.DerivativeChainPrivate.chainCost z ≤ Real.sqrt (n+1-m+1 : ℕ)*Real.sqrt (R^2-‖_root_.DerivativeChainContinuation.rootCentroid p-o‖^2) := by
  have hpne : p ≠ 0 := by intro he; rw [he,natDegree_zero] at hdegree; omega
  have hlead : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hpne
  let c := p.leadingCoeff⁻¹
  have hc : c ≠ 0 := inv_ne_zero hlead
  let P : Polynomial ℂ := C c*p
  have hP : P.Monic := monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hlead)
  have hPdegree : P.natDegree=n+1 := by simpa only [P,natDegree_C_mul hc] using hdegree
  have hcentroid : _root_.DerivativeChainContinuation.rootCentroid P=_root_.DerivativeChainContinuation.rootCentroid p := by
    simp only [_root_.DerivativeChainContinuation.rootCentroid,P,roots_C_mul _ hc,natDegree_C_mul hc]
  have hPcore : (derivative^[n+1-m] P).comp (C (_root_.DerivativeChainContinuation.rootCentroid P)+C σ*X)=
      C (c*C₀)*_root_.DerivativeChainPrivate.spokePoly k r q := by
    rw [hcentroid]
    change (derivative^[n+1-m] (C c*p)).comp (C (_root_.DerivativeChainContinuation.rootCentroid p)+C σ*X)=_
    rw [iterate_derivative_C_mul,Polynomial.mul_comp,Polynomial.C_comp,hcore]
    rw [←mul_assoc,←map_mul]
  have hPdisk (w : ℂ) (hw : P.eval w=0) : ‖w-o‖ ≤ R := by
    apply ha w
    change (C c*p).eval w=0 at hw
    simp only [eval_mul,eval_C] at hw
    exact (mul_eq_zero.mp hw).resolve_left hc
  obtain ⟨z,hz,hz0,hcost⟩ := _root_.DerivativeChainExtremal.monic_polynomial_radial_prefix P hP n m k r hPdegree q σ
    (c*C₀) o R hm hmn hk hr hq (mul_ne_zero hc hC) hσ hPcore hR hPdisk
  refine ⟨z,?_,?_,?_⟩
  · intro i
    have hh := hz i
    change (derivative^[n+1-(i.val+1)] (C c*p)).eval (z i)=0 at hh
    rw [iterate_derivative_C_mul,eval_mul,eval_C] at hh
    exact (mul_eq_zero.mp hh).resolve_left hc
  · simpa only [hcentroid] using hz0
  · simpa only [hcentroid] using hcost

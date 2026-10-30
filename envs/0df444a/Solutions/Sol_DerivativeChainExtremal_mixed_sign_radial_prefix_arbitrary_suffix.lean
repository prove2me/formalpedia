-- Prove2me | solution 1 for DerivativeChainExtremal.mixed_sign_radial_prefix_arbitrary_suffix
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:07:56.648012+00:00
-- url     : https://prove2.me/submissions/4fa1b6f1-8c00-4552-a4ec-1ac782ac0d8e

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainExtremal_actual_balanced_radial_prefix_extension
import Theorems.Thm_DerivativeChainExtremal_spoke_balanced_geodesic_prefix
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


open Polynomial DerivativeChainPrivate
set_option autoImplicit false



set_option autoImplicit false

namespace DerivativeChainPrivate









end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial









end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators

namespace DerivativeChainPrivate













end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
open scoped BigOperators
namespace DerivativeChainPrivate







end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial







end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate











end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate







end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial

theorem iterate_derivative_comp_affine (p : Polynomial ℂ) (a c : ℂ) (k : ℕ) :
    derivative^[k] (p.comp (C a+C c*X)) =
      C (c^k)*(derivative^[k] p).comp (C a+C c*X) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih,derivative_C_mul,derivative_comp]
    simp only [derivative_add,derivative_C,derivative_mul,zero_mul,derivative_X,
      mul_one,zero_add,Function.iterate_succ_apply']
    rw [pow_succ,C_mul]
    ring

theorem affine_derivative_root (P Q : Polynomial ℂ) (a c d : ℂ) (hc : c ≠ 0)
    (hcomp : P.comp (C a+C c*X) = C d*Q) (k : ℕ) (z : ℂ)
    (hz : (derivative^[k] Q).eval z = 0) :
    (derivative^[k] P).eval (a+c*z) = 0 := by
  have h := congrArg (fun p : Polynomial ℂ => (derivative^[k] p).eval z) hcomp
  rw [iterate_derivative_comp_affine,iterate_derivative_C_mul] at h
  simp only [eval_mul,eval_C,eval_comp,eval_add,eval_X,hz,mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero k hc)





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial







end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
open Filter Topology
namespace DerivativeChainPrivate
open Polynomial











end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate









end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate




set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators













theorem complex_iterate_derivative_natDegree (p : Polynomial ℂ) (j : ℕ) :
    (derivative^[j] p).natDegree=p.natDegree-j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply',natDegree_derivative,ih]
    omega










end DerivativeChainContinuation


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators

theorem actual_complex_source_natDegree {n : ℕ} (a : Fin (n+1) → ℂ) :
    (fromRoots a).natDegree=n+1 := by
  simp only [fromRoots]
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (a i))]
  simp

theorem actual_complex_row_natDegree {n : ℕ} (a : Fin (n+1) → ℂ)
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n+1) : (row a m).natDegree=m := by
  rw [row,complex_iterate_derivative_natDegree,actual_complex_source_natDegree]
  omega






















end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace DerivativeChainExtremal
open Polynomial DerivativeChainPrivate DerivativeChainContinuation
open scoped BigOperators

theorem actual_affine_radial_prefix_law {n : ℕ} (a : Fin (n+1) → ℂ)
    (m k r : ℕ) (q : Polynomial ℝ) (u σ C₀ : ℂ)
    (hm : 1 ≤ m) (hmn : m ≤ n+1) (hk : 2 ≤ k) (hr : r < k)
    (hq : q.Splits) (hC : C₀ ≠ 0) (hσ : ‖σ‖=1)
    (hcore : (row a m).comp (C u+C σ*X)=C C₀*spokePoly k r q) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ∃ (ι : Type) (inst : Fintype ι), letI := inst;
      ∃ (π : ι → ℝ) (f : ι → ℕ → ℂ),
        (∀ i, 0 ≤ π i) ∧ (∑ i, π i=1) ∧ (∀ i, f i 0=u) ∧
        (∀ i j, j < m → (row a (j+1)).eval (f i j)=0) ∧
        (∀ i, ‖f i (m-1)-u‖=ρ) ∧ (∑ i, (π i:ℂ)*f i (m-1)=u) ∧
        (∀ i, (∑ j∈Finset.range (m-1), ‖f i (j+1)-f i j‖)=ρ) := by
  classical
  have hσne : σ ≠ 0 := by intro he; simp [he] at hσ
  have hdegree : (spokePoly k r q).natDegree=m := by
    have hd := congrArg natDegree hcore
    rw [natDegree_comp,natDegree_C_add,natDegree_C_mul_X _ hσne,mul_one,
      natDegree_C_mul hC,actual_complex_row_natDegree a m hm hmn] at hd
    exact hd.symm
  have hqne : q ≠ 0 := by
    intro he
    have hz : spokePoly k r q=0 := by simp [spokePoly,he]
    rw [hz,natDegree_zero] at hdegree
    omega
  obtain ⟨ρ,hρ,ι,inst,hdata⟩ := spoke_balanced_geodesic_prefix m k r q hm hk hr hq hqne hdegree
  letI : Fintype ι := inst
  obtain ⟨π,g,hπ0,hπsum,hg0,hgr,hgn,hgm,hgc⟩ := hdata
  let f : ι → ℕ → ℂ := fun i j => u+σ*g i j
  refine ⟨ρ,hρ,ι,inst,π,f,hπ0,hπsum,?_,?_,?_,?_,?_⟩
  · intro i; simp only [f,hg0,mul_zero,add_zero]
  · intro i j hj
    have he := affine_derivative_root (row a m) (spokePoly k r q) u σ C₀
      hσne hcore (m-(j+1)) (g i j) (hgr i j hj)
    unfold row at he ⊢
    rw [←Function.iterate_add_apply,
      show (m-(j+1))+(n+1-m)=n+1-(j+1) by omega] at he
    exact he
  · intro i
    change ‖u+σ*g i (m-1)-u‖=ρ
    rw [add_sub_cancel_left,norm_mul,hσ,one_mul,hgn]
  · have he (i : ι) : (π i:ℂ)*(u+σ*g i (m-1)) =
        (π i:ℂ)*u+σ*((π i:ℂ)*g i (m-1)) := by ring
    simp only [f,he,Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum,
      ←Complex.ofReal_sum,hπsum,Complex.ofReal_one,one_mul,hgm,mul_zero,add_zero]
  · intro i
    simpa only [f,add_sub_add_left_eq_sub,←mul_sub,norm_mul,hσ,one_mul] using hgc i





end DerivativeChainExtremal


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open DerivativeChainExtremal
open Polynomial DerivativeChainPrivate DerivativeChainContinuation
open scoped BigOperators



theorem solution {n : ℕ} (a : Fin (n+1) → ℂ)
    (m k r : ℕ) (q : Polynomial ℝ) (σ C₀ o : ℂ) (R : ℝ)
    (hm : 1 ≤ m) (hmn : m ≤ n+1) (hk : 2 ≤ k) (hr : r < k)
    (hq : q.Splits) (hC : C₀ ≠ 0) (hσ : ‖σ‖=1)
    (hcore : (_root_.DerivativeChainPrivate.row a m).comp (C (_root_.DerivativeChainContinuation.complexCentroid a)+C σ*X)=C C₀*_root_.DerivativeChainPrivate.spokePoly k r q)
    (hR : 0 ≤ R) (ha : ∀ i, ‖a i-o‖ ≤ R) :
    ∃ z : Fin (n+1) → ℂ, _root_.DerivativeChainPrivate.IsChain a z ∧ z 0=_root_.DerivativeChainContinuation.complexCentroid a ∧
      _root_.DerivativeChainPrivate.chainCost z ≤ Real.sqrt (n+1-m+1 : ℕ)*Real.sqrt (R^2-‖_root_.DerivativeChainContinuation.complexCentroid a-o‖^2) := by
  obtain ⟨ρ,hρ,ι,inst,hdata⟩ := _root_.DerivativeChainExtremal.actual_affine_radial_prefix_law a m k r q
    (_root_.DerivativeChainContinuation.complexCentroid a) σ C₀ hm hmn hk hr hq hC hσ hcore
  letI : Fintype ι := inst
  obtain ⟨π,f,hπ0,hπsum,hf0,hfr,hfn,hfm,hfc⟩ := hdata
  exact _root_.DerivativeChainExtremal.actual_balanced_radial_prefix_extension a m hm hmn (_root_.DerivativeChainContinuation.complexCentroid a) o R ρ
    hR hρ ha π f hπ0 hπsum hf0 hfr hfn hfm hfc

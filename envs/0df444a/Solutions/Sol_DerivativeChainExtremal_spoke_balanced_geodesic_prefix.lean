-- Prove2me | solution 1 for DerivativeChainExtremal.spoke_balanced_geodesic_prefix
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:05:49.274239+00:00
-- url     : https://prove2.me/submissions/140fc99b-307b-41b0-8427-0e2d6981ddc2

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Theorems.Thm_DerivativeChainContinuation_binomial_root_law
import Theorems.Thm_DerivativeChainPrivate_spoke_geodesic
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
open DerivativeChainPrivate
open scoped BigOperators







theorem geodesic_prefix_cost (M : ℕ) (f : ℕ → ℂ) (hf0 : f 0=0)
    (hstep : ∀ i < M-1, ‖f (i+1)-f i‖ = ‖f (i+1)‖-‖f i‖) :
    (∑ i ∈ Finset.range (M-1), ‖f (i+1)-f i‖) = ‖f (M-1)‖ := by
  calc
    _ = ∑ i ∈ Finset.range (M-1), (‖f (i+1)‖-‖f i‖) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hstep i (Finset.mem_range.mp hi)
    _ = _ := by rw [Finset.sum_range_sub (fun i => ‖f i‖),hf0,norm_zero,sub_zero]





end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators

theorem positive_spoke_rotation_comp (k r : ℕ) (Q : Polynomial ℝ)
    (ζ : ℂ) (hζ : ζ^k=1) :
    (spokePoly k r Q).comp (C 0+C ζ*X)=C (ζ^r)*spokePoly k r Q := by
  simp only [spokePoly,Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.X_comp,
    C_0,zero_add,Polynomial.comp_assoc,mul_pow,←map_pow,hζ,map_one,one_mul]
  ring








































end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace DerivativeChainExtremal
open Polynomial DerivativeChainPrivate DerivativeChainContinuation
open scoped BigOperators

theorem spoke_derivative_rotation_root (k r j : ℕ) (q : Polynomial ℝ)
    (ζ z : ℂ) (hζ : ζ^k=1) (hζne : ζ ≠ 0)
    (hz : (derivative^[j] (spokePoly k r q)).eval z=0) :
    (derivative^[j] (spokePoly k r q)).eval (ζ*z)=0 := by
  have h := affine_derivative_root (spokePoly k r q) (spokePoly k r q)
    0 ζ (ζ^r) hζne (positive_spoke_rotation_comp k r q ζ hζ) j z hz
  simpa using h





end DerivativeChainExtremal


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open DerivativeChainExtremal
open Polynomial DerivativeChainPrivate DerivativeChainContinuation
open scoped BigOperators



theorem solution (m k r : ℕ) (q : Polynomial ℝ)
    (hm : 1  ≤  m) (hk : 2  ≤  k) (hr : r  <  k) (hq : q.Splits) (hqne : q  ≠  0)
    (hdegree : (_root_.DerivativeChainPrivate.spokePoly k r q).natDegree=m) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ∃ (ι : Type) (inst : Fintype ι), letI := inst;
      ∃ (π : ι → ℝ) (f : ι → ℕ → ℂ),
        (∀ i,0 ≤ π i) ∧ (∑ i,π i=1) ∧ (∀ i,f i 0=0) ∧
        (∀ i j,j < m → (derivative^[m-(j+1)] (_root_.DerivativeChainPrivate.spokePoly k r q)).eval (f i j)=0) ∧
        (∀ i,‖f i (m-1)‖=ρ) ∧ (∑ i,(π i:ℂ)*f i (m-1)=0) ∧
        (∀ i,(∑ j∈Finset.range (m-1),‖f i (j+1)-f i j‖)=ρ) := by
  classical
  obtain ⟨z,hz0,hzr,hzs⟩ := _root_.DerivativeChainPrivate.spoke_geodesic (m-1) k r q hk hr hq hqne (by omega)
  have hroots (j : ℕ) (hj : j < m) :
      (derivative^[m-(j+1)] (_root_.DerivativeChainPrivate.spokePoly k r q)).eval (z j)=0 := by
    have h := hzr j (by omega)
    simpa only [show m-1-j=m-(j+1) by omega] using h
  have hcost : (∑ j∈Finset.range (m-1),‖z (j+1)-z j‖)=‖z (m-1)‖ :=
    _root_.DerivativeChainContinuation.geodesic_prefix_cost m z hz0 hzs
  let b := z (m-1)
  by_cases hb : b=0
  · refine ⟨0,le_rfl,Unit,inferInstance,(fun _ => 1),(fun _ => z),?_,?_,?_,?_,?_,?_,?_⟩
    · intro i; norm_num
    · simp
    · intro i; exact hz0
    · intro i j hj; exact hroots j hj
    · intro i; change ‖b‖=0; simp [hb]
    · simpa only [Fintype.sum_unique,Complex.ofReal_one,one_mul] using
        (show z (m-1)=0 from hb)
    · intro i
      have h : (∑ j∈Finset.range (m-1),‖z (j+1)-z j‖)=‖b‖ := hcost
      simpa only [hb,norm_zero] using h
  · let F : Polynomial ℂ := X^k+C (-(b^k))
    let ι := F.roots.toFinset
    obtain ⟨π,hπ0,hπs,hπm,hpow,_⟩ := _root_.DerivativeChainContinuation.binomial_root_law k hk (-(b^k))
    let ζ : ι → ℂ := fun i => (i:ℂ)/b
    have hζpow (i : ι) : (ζ i)^k=1 := by
      dsimp only [ζ]
      rw [div_pow,hpow i,neg_neg,div_self (pow_ne_zero k hb)]
    have hζne (i : ι) : ζ i ≠ 0 := by
      intro hz
      have hh := hζpow i
      rw [hz,zero_pow (show k ≠ 0 by omega)] at hh
      exact zero_ne_one hh
    have hζnorm (i : ι) : ‖ζ i‖=1 := by
      apply (pow_left_inj₀ (norm_nonneg _) (by positivity) (show k ≠ 0 by omega)).mp
      rw [←norm_pow,hζpow,norm_one,one_pow]
    let f : ι → ℕ → ℂ := fun i j => ζ i*z j
    refine ⟨‖b‖,norm_nonneg _,ι,inferInstance,π,f,hπ0,hπs,?_,?_,?_,?_,?_⟩
    · intro i; simp [f,hz0]
    · intro i j hj
      exact _root_.DerivativeChainExtremal.spoke_derivative_rotation_root k r (m-(j+1)) q (ζ i) (z j)
        (hζpow i) (hζne i) (hroots j hj)
    · intro i; change ‖ζ i*b‖=‖b‖; rw [norm_mul,hζnorm,one_mul]
    · have he (i : ι) : f i (m-1)=(i:ℂ) := by
        change (i:ℂ)/b*b=(i:ℂ)
        exact div_mul_cancel₀ _ hb
      simpa only [he] using hπm
    · intro i
      simpa only [f,←mul_sub,norm_mul,hζnorm,one_mul] using hcost

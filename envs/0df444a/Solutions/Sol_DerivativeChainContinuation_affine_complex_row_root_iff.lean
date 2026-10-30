-- Prove2me | solution 1 for DerivativeChainContinuation.affine_complex_row_root_iff
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T21:06:22.110324+00:00
-- url     : https://prove2.me/submissions/d1bb87d4-761c-499b-87cf-0957257a0e5f

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
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

theorem affine_complex_source_comp {n : ℕ} (a : Fin (n+1) → ℂ) (o c : ℂ) :
    (fromRoots (fun i => o+c*a i)).comp (C o+C c*X)=C (c^(n+1))*fromRoots a := by
  have hf (i : Fin (n+1)) : (X-C (o+c*a i)).comp (C o+C c*X)=C c*(X-C (a i)) := by
    rw [sub_comp,X_comp,C_comp]
    simp only [map_add,map_mul]
    ring
  simp only [fromRoots,Polynomial.prod_comp,hf,Finset.prod_mul_distrib]
  simp
























end DerivativeChainContinuation


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



theorem solution {n : ℕ} (a : Fin (n+1) → ℂ)
    (o c : ℂ) (hc : c≠0) (m : ℕ) (z : ℂ) :
    (row (fun i => o+c*a i) m).eval (o+c*z)=0 ↔ (row a m).eval z=0 := by
  have he := congrArg (fun p : Polynomial ℂ => (derivative^[n+1-m] p).eval z)
    (affine_complex_source_comp a o c)
  rw [iterate_derivative_comp_affine,iterate_derivative_C_mul] at he
  simp only [eval_mul,eval_C,eval_comp,eval_add,eval_X] at he
  change c^(n+1-m)*(row (fun i => o+c*a i) m).eval (o+c*z)=
    c^(n+1)*(row a m).eval z at he
  constructor
  · intro h
    rw [h,mul_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero _ hc)
  · intro h
    rw [h,mul_zero] at he
    exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ hc)

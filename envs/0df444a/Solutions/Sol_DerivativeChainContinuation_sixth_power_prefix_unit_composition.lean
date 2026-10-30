-- Prove2me | solution 1 for DerivativeChainContinuation.sixth_power_prefix_unit_composition
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:33:20.636933+00:00
-- url     : https://prove2.me/submissions/bb5392e3-9c65-4f81-9c4e-f28a9742b3e9

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SixthPhysicalNormalization
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate





theorem sixth_prefix_radius_positive : 0<sixthPrefixRadius := by
  unfold sixthPrefixRadius
  positivity

theorem sixth_prefix_radius_sq : sixthPrefixRadius^2=17/2 :=
  Real.sq_sqrt (by norm_num)









theorem sixth_prefix_unit_composition (β : ℂ) :
    (X^3-C (17/2)*X-136*C β : Polynomial ℂ).comp (C 0+C (sixthPrefixRadius:ℂ)*X)=
      C ((sixthPrefixRadius:ℂ)^3)*(X^3-X-C (sixthPhysicalParameter β)) := by
  have hr : (sixthPrefixRadius:ℂ)≠0 := by exact_mod_cast sixth_prefix_radius_positive.ne'
  have hr2 : (sixthPrefixRadius:ℂ)^2=17/2 := by
    rw [←Complex.ofReal_pow,sixth_prefix_radius_sq]
    norm_num
  have hr3 : (sixthPrefixRadius:ℂ)^3=(17/2)*(sixthPrefixRadius:ℂ) := by
    calc
      _=(sixthPrefixRadius:ℂ)^2*(sixthPrefixRadius:ℂ) := by ring
      _=_ := by rw [hr2]
  have hβ : (sixthPrefixRadius:ℂ)^3*sixthPhysicalParameter β=136*β := by
    unfold sixthPhysicalParameter
    field_simp
  apply Polynomial.funext
  intro z
  simp only [eval_comp,eval_add,eval_sub,eval_mul,eval_pow,eval_X,eval_C,eval_ofNat,zero_add]
  linear_combination z*hr3+hβ











end DerivativeChainContinuation

theorem solution (β : ℂ) :
    ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ).comp (C 0+C (sixthPrefixRadius:ℂ)*X)=
      C ((sixthPrefixRadius:ℂ)^18)*(X^3-X-C (sixthPhysicalParameter β))^6 := by
  rw [Polynomial.pow_comp,sixth_prefix_unit_composition,mul_pow,←Polynomial.C_pow]
  congr 1
  ring

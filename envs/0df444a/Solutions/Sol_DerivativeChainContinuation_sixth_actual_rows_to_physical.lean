-- Prove2me | solution 1 for DerivativeChainContinuation.sixth_actual_rows_to_physical
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:39:43.71018+00:00
-- url     : https://prove2.me/submissions/9f392530-4898-40db-9aad-1782d29f78a7

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SixthPhysicalNormalization
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_sixth_actual_rows_rescale
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























end DerivativeChainContinuation

theorem solution (β z : ℂ) (k : ℕ) :
    (derivative^[k] ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ)).eval z=0 ↔
      (derivative^[k] ((X^3-X-C (sixthPhysicalParameter β))^6 : Polynomial ℂ)).eval
        ((sixthPhysicalScale:ℂ)*z)=0 := by
  have hr : (sixthPrefixRadius:ℂ)≠0 := by exact_mod_cast sixth_prefix_radius_positive.ne'
  have hz : (sixthPrefixRadius:ℂ)*((sixthPhysicalScale:ℂ)*z)=z := by
    unfold sixthPhysicalScale
    push_cast
    field_simp
  simpa only [hz] using sixth_actual_rows_rescale β ((sixthPhysicalScale:ℂ)*z) k

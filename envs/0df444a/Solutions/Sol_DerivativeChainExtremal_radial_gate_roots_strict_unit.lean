-- Prove2me | solution 1 for DerivativeChainExtremal.radial_gate_roots_strict_unit
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:28:12.7236+00:00
-- url     : https://prove2.me/submissions/e9a04789-2d8f-421a-80b8-e0d763327ca0

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_ExtremalGateExample
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
set_option maxHeartbeats 2500000
open DerivativeChainExtremal
open Polynomial DerivativeChainPrivate DerivativeChainContinuation













theorem solution (z : ℂ) (hz : _root_.DerivativeChainExtremal.radialGateExample.eval z=0) : ‖z‖ < 1 := by
  by_contra h
  have hz1 : 1 ≤ ‖z‖ := le_of_not_gt h
  have he : (3072:ℂ)*z^10=(1600:ℂ)*z^6-(240:ℂ)*z^2-15*Complex.I := by
    simp only [_root_.DerivativeChainExtremal.radialGateExample,eval_add,eval_sub,eval_mul,eval_C,eval_pow,eval_X] at hz
    linear_combination hz
  have htri : ‖(1600:ℂ)*z^6-(240:ℂ)*z^2-15*Complex.I‖ ≤
      1600*‖z‖^6+240*‖z‖^2+15 := by
    calc
      _ ≤ ‖(1600:ℂ)*z^6-(240:ℂ)*z^2‖+‖15*Complex.I‖ := norm_sub_le _ _
      _ ≤ (‖(1600:ℂ)*z^6‖+‖(240:ℂ)*z^2‖)+‖15*Complex.I‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ = _ := by norm_num [norm_mul,norm_pow]
  have hlead : 3072*‖z‖^10 ≤ 1600*‖z‖^6+240*‖z‖^2+15 := by
    have hh := congrArg norm he
    norm_num [norm_mul,norm_pow] at hh
    linarith
  have h6 : ‖z‖^6 ≤ ‖z‖^10 := pow_le_pow_right₀ hz1 (by norm_num)
  have h2 : ‖z‖^2 ≤ ‖z‖^10 := pow_le_pow_right₀ hz1 (by norm_num)
  have h10 : 1 ≤ ‖z‖^10 := one_le_pow₀ hz1
  nlinarith

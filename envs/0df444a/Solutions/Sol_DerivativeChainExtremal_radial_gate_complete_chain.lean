-- Prove2me | solution 1 for DerivativeChainExtremal.radial_gate_complete_chain
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:30:06.130918+00:00
-- url     : https://prove2.me/submissions/d2d245aa-ad59-4857-935c-4fe926508f6b

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_ExtremalGateExample
import Definitions.Def_DerivativeChainContinuation_CenteredSource
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainExtremal_radial_gate_centroid
import Theorems.Thm_DerivativeChainExtremal_radial_gate_degree
import Theorems.Thm_DerivativeChainExtremal_radial_gate_derivative
import Theorems.Thm_DerivativeChainExtremal_radial_gate_real_quotient
import Theorems.Thm_DerivativeChainExtremal_radial_gate_roots_strict_unit
import Theorems.Thm_DerivativeChainExtremal_real_quotient_critical_row_sqrt_two
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















theorem solution :
    ∃ z : Fin 10 → ℂ,
      (∀ i, (derivative^[10-(i.val+1)] _root_.DerivativeChainExtremal.radialGateExample).eval (z i)=0) ∧ z 0=0 ∧
      _root_.DerivativeChainPrivate.chainCost z ≤ Real.sqrt 2 := by
  have hcore : _root_.DerivativeChainExtremal.radialGateExample.derivative.comp (C (_root_.DerivativeChainContinuation.rootCentroid _root_.DerivativeChainExtremal.radialGateExample)+C 1*X)=
      C 480*_root_.DerivativeChainPrivate.spokePoly 4 1 _root_.DerivativeChainExtremal.radialGateQuotient := by
    rw [_root_.DerivativeChainExtremal.radial_gate_centroid]
    simpa using _root_.DerivativeChainExtremal.radial_gate_derivative
  obtain ⟨z,hzr,hz0,hzc⟩ := _root_.DerivativeChainExtremal.real_quotient_critical_row_sqrt_two _root_.DerivativeChainExtremal.radialGateExample 9 4 1
    (by norm_num) _root_.DerivativeChainExtremal.radial_gate_degree _root_.DerivativeChainExtremal.radialGateQuotient 1 480 0 1 (by norm_num) (by norm_num)
    _root_.DerivativeChainExtremal.radial_gate_real_quotient (by norm_num) (by norm_num) hcore (by norm_num)
    (fun w hw => by simpa only [sub_zero] using (_root_.DerivativeChainExtremal.radial_gate_roots_strict_unit w hw).le)
  exact ⟨z,hzr,by simpa only [_root_.DerivativeChainExtremal.radial_gate_centroid] using hz0,
    by simpa only [_root_.DerivativeChainExtremal.radial_gate_centroid,sub_self,norm_zero,zero_pow (by norm_num : 2 ≠ 0),
      one_pow,sub_zero,Real.sqrt_one,mul_one] using hzc⟩

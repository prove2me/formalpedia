-- Prove2me | solution 1 for DerivativeChainExtremal.radial_gate_derivative
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:24:20.59415+00:00
-- url     : https://prove2.me/submissions/4716ac59-fd60-4a78-9a7f-7c94a0175899

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_ExtremalGateExample
import Definitions.Def_DerivativeChainPrivate_SpokeRows
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









theorem solution : _root_.DerivativeChainExtremal.radialGateExample.derivative=C 480*_root_.DerivativeChainPrivate.spokePoly 4 1 _root_.DerivativeChainExtremal.radialGateQuotient := by
  simp only [_root_.DerivativeChainExtremal.radialGateExample,_root_.DerivativeChainExtremal.radialGateQuotient,_root_.DerivativeChainPrivate.spokePoly,derivative_add,derivative_sub,
    derivative_C_mul,derivative_X_pow,derivative_C,add_zero,Polynomial.map_add,
    Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,
    Polynomial.map_X,Polynomial.map_one,Polynomial.add_comp,Polynomial.sub_comp,
    Polynomial.mul_comp,Polynomial.C_comp,Polynomial.pow_comp,Polynomial.X_comp,Polynomial.one_comp]
  norm_num [Polynomial.C_ofNat]
  ring

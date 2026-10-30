-- Prove2me | solution 1 for DerivativeChainExtremal.radial_gate_degree
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:20:35.38174+00:00
-- url     : https://prove2.me/submissions/f0b5d846-6b07-4683-8e33-269d7e1ef747

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





theorem solution : _root_.DerivativeChainExtremal.radialGateExample.natDegree=10 := by
  unfold _root_.DerivativeChainExtremal.radialGateExample
  compute_degree <;> norm_num

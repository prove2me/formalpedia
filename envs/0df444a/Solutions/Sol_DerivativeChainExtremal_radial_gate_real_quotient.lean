-- Prove2me | solution 1 for DerivativeChainExtremal.radial_gate_real_quotient
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:26:15.316115+00:00
-- url     : https://prove2.me/submissions/cad86997-51ac-4577-a5d0-f6fdb494c7a9

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











theorem solution : _root_.DerivativeChainExtremal.radialGateQuotient.Splits := by
  have he : _root_.DerivativeChainExtremal.radialGateQuotient=(C 16*X-1)*(C 4*X-1) := by
    unfold _root_.DerivativeChainExtremal.radialGateQuotient
    norm_num [Polynomial.C_ofNat]
    ring
  rw [he]
  exact (Splits.of_natDegree_le_one (by compute_degree)).mul
    (Splits.of_natDegree_le_one (by compute_degree))

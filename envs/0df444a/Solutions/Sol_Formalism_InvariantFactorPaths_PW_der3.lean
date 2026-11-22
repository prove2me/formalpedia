-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.der3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:44:09.615707+00:00
-- url     : https://prove2.me/submissions/f9042ccc-9150-4844-8a96-701bc7baab63

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset
variable {R : Type} [Ring R]
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (x f o e f' o' e' : R) (hf : x * f = f * x + f') (ho : x * o = o * x + o')
    (he : x * e = e * x + e') :
    x * (f * o * e) = (f * o * e) * x + (f' * o * e + f * o' * e + f * o * e') := by
  calc x * (f * o * e) = (x * f) * o * e := by simp only [mul_assoc]
    _ = f * (x * o) * e + f' * o * e := by rw [hf]; simp only [add_mul, mul_assoc]
    _ = f * o * (x * e) + f * o' * e + f' * o * e := by rw [ho]; simp only [add_mul, mul_add, mul_assoc]
    _ = (f * o * e) * x + (f' * o * e + f * o' * e + f * o * e') := by
        rw [he]; simp only [mul_add, mul_assoc]; abel
end Formalism.InvariantFactorPaths.PW

-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.Pstep_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:55.296323+00:00
-- url     : https://prove2.me/submissions/60e76037-6a60-4406-a58d-4a9f834f5eaa

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
variable {K W ι : Type} [Field K] [AddCommGroup W] [Module K W] [DecidableEq ι]
variable {E : ι → ι → Module.End K W}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (S : Finset ι) (z : ι) (l : ℕ) (X : Module.End K W)
    (hX : ∀ q, X * Om E S z q = Om E S z q * X) : X * Pstep E S z l = Pstep E S z l * X := by
  simp only [Pstep, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, hX]
end Formalism.InvariantFactorPaths.PW

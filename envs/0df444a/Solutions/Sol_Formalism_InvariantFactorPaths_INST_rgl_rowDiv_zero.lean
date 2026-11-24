-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.rgl_rowDiv_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:48.025857+00:00
-- url     : https://prove2.me/submissions/7d150fbf-b19c-4250-b374-88f782c2af88

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_GlFirstLineDividedPowers
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_rowDiv_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_rowDiv_C_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_rowDiv_X_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.INST
open Formalism.GradedWeylDivisibility Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.InvariantFactorPaths.PW
variable (R : Type) [CommRing R] {r n : ℕ}
namespace Formalism.InvariantFactorPaths.INST
theorem _root_.solution (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) R) : rowDiv R a b 0 f = f := by
  induction f using MvPolynomial.induction_on with
  | C c => exact rgl_rowDiv_C_zero R a b c
  | add f g hf hg => rw [rowDiv_add, hf, hg]
  | mul_X f v hf =>
    rw [rgl_rowDiv_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, hf, rgl_rowDiv_X_zero]
end Formalism.InvariantFactorPaths.INST

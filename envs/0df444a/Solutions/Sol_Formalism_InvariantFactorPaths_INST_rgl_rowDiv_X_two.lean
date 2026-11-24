-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.rgl_rowDiv_X_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:47.522844+00:00
-- url     : https://prove2.me/submissions/96e82563-df36-4286-a2ba-4855b7f7c0d6

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_GlFirstLineDividedPowers
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_rowGen_X

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
theorem _root_.solution (a b : Fin r) (k : ℕ) (v : Fin r × Fin n) :
    rowDiv R a b (k + 2) (X v) = 0 := by
  rw [rowDiv, rgl_rowGen_X]
  split_ifs
  · rw [Polynomial.coeff_add, Polynomial.coeff_C_succ, Polynomial.coeff_X_mul, Polynomial.coeff_C_succ, add_zero]
  · rw [add_zero, Polynomial.coeff_C_succ]
end Formalism.InvariantFactorPaths.INST

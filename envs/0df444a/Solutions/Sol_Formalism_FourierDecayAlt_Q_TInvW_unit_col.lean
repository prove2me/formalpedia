-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.unit_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:57:51.745597+00:00
-- url     : https://prove2.me/submissions/a6b7bf1b-f9cc-45e0-8bfd-f85c45fad587

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceRestriction
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceCongruence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.TInvW
theorem _root_.solution (i : Fin (r + 1)) (p q : Fin (mdim k r i)) (c : Fin (2 * r + k + 1))
    (hcq : c ≠ posL k r i q) (hHc : Hpk k r (posL k r i p) c = 0) (x : Fin (2 * r + k + 1)) :
    (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ)) x c = 0 ∧
    (Hpk k r * (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ))ᴴ * Hpk k r) x c = 0 := by
  constructor
  · simp [Matrix.single_apply, hcq, Ne.symm hcq]
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l = posL k r i p
    · rw [hl, hHc, mul_zero]
    · have h0 : (Hpk k r * (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ))ᴴ) x l = 0 := by
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_zero fun m _ => ?_
        simp [Matrix.conjTranspose_apply, Matrix.single_apply, hl, Ne.symm hl]
      rw [h0, zero_mul]
end Formalism.FourierDecayAlt.Q.TInvW

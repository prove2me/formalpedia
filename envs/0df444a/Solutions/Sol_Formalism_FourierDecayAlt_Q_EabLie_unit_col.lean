-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabLie.unit_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:49:28.257881+00:00
-- url     : https://prove2.me/submissions/d6e884e6-8194-4318-b15c-dc4df0555d00

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DerivativePreservation_HasDerivAtExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabLie
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.EabLie
theorem _root_.solution (i : Fin (r + 1)) (p q : Fin (mdim k r i)) (c : Fin (2 * r + k + 1))
    (hcq : c ≠ posL k r i q) (hHc : Hpk k r (posL k r i p) c = 0) (x : Fin (2 * r + k + 1)) :
    (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ)) x c = 0 ∧
    (Hpk k r * (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ))ᴴ * Hpk k r) x c = 0 := by
  constructor
  · simp [Ne.symm hcq]
  · rw [Matrix.mul_assoc, Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun y _ => ?_)
    have : ((Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ))ᴴ * Hpk k r) y c = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero (fun z _ => ?_)
      rw [conjTranspose_apply, Matrix.single_apply]
      split_ifs with h
      · rw [← h.1, hHc, mul_zero]
      · simp
    rw [this, mul_zero]
end Formalism.FourierDecayAlt.Q.EabLie

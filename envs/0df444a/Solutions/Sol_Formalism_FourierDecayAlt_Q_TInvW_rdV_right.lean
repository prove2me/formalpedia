-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.rdV_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:56:17.9432+00:00
-- url     : https://prove2.me/submissions/bf620f17-00e0-4ddb-8269-df4e13c95337

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
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (X s' g : Mx k r) (f : Mx k r → E)
    (hu1 : s' * s'⁻¹ = 1) (hu2 : s'⁻¹ * s' = 1) :
    RdV X (fun x => f (x * s')) g = RdV (s'⁻¹ * X * s') f (g * s') := by
  have hU : IsUnit s' := ⟨⟨s', s'⁻¹, hu1, hu2⟩, rfl⟩
  simp only [RdV]
  congr 1
  funext t
  congr 1
  rw [show ((t : ℂ) • (s'⁻¹ * X * s')) = s'⁻¹ * ((t : ℂ) • X) * s' by rw [mul_smul_comm, smul_mul_assoc],
    Matrix.exp_conj' _ _ hU]
  simp only [mul_assoc]
  rw [← mul_assoc s' s'⁻¹, hu1, one_mul]
end Formalism.FourierDecayAlt.Q.TInvW

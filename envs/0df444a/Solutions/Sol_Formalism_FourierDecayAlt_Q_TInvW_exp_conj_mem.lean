-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.exp_conj_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:55:21.9788+00:00
-- url     : https://prove2.me/submissions/193d942a-855b-4e26-9749-66c17c91f703

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceRestriction
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceCongruence
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_glev_inv
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_glev_unit
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_TInvW_glev_mul__c26af469cc3a


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
theorem _root_.solution {i : Fin (r + 1)} {s : Mx k r} (hs : s ∈ Glev k r i) {X : Mx k r}
    (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • (s⁻¹ * X * s)) ∈ Glev k r i := by
  have hu := glev_unit hs
  have hU : IsUnit s := ⟨⟨s, s⁻¹, hu.1, hu.2⟩, rfl⟩
  rw [show ((t : ℂ) • (s⁻¹ * X * s)) = s⁻¹ * ((t : ℂ) • X) * s by rw [mul_smul_comm, smul_mul_assoc],
    Matrix.exp_conj' _ _ hU]
  exact glev_mul' (glev_mul' (glev_inv hs) (hX t)) hs
end Formalism.FourierDecayAlt.Q.TInvW

-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.transfer_invariance_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:12:32.480533+00:00
-- url     : https://prove2.me/submissions/de38e986-474e-4e43-8114-07566a1efa0c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceRestriction
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_TInvW_glev_mul__c26af469cc3a
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_n_fix
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_h_fix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.TInvW
theorem _root_.solution : StepS := by
  intro k r z i hz
  have hUW : ∀ h ∈ UWset k r z, h ∈ Glev k r i := by
    intro h hh
    simp only [UWset, Glev, Set.mem_setOf_eq] at hh ⊢
    exact ⟨hh.1, fun a _ => hh.2.1 a⟩
  simp only [Slev, Set.mem_setOf_eq]
  refine ⟨⟨1, ?_, 1, ?_, (mul_one 1).symm⟩, ?_⟩
  · simp [UWset, UH]
  · simp [Nlev, QuantumDeterminants.Nset, Glev, UH, Matrix.one_apply]
  · rintro s ⟨h, hh, m, hm, rfl⟩
    have hmG : m ∈ Glev k r i := by
      unfold Nlev at hm
      exact hm.2
    refine ⟨glev_mul' (hUW h hh) hmG, ?_⟩
    rw [← Matrix.mulVec_mulVec, n_fix hz hm, h_fix hh]
end Formalism.FourierDecayAlt.Q.TInvW

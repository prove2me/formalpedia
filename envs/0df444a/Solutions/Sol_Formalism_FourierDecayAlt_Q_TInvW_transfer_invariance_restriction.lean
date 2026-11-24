-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.transfer_invariance_restriction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:57:50.287501+00:00
-- url     : https://prove2.me/submissions/12a3e06b-0e49-4a9c-a017-1f6e0ac37278

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceRestriction
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_TInvW_glev_mul__c26af469cc3a

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
theorem _root_.solution : StepRSm := by
  intro E _ _ k r i D f s' hs' hD hf g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf (g₀ * s') ⟨glev_mul' hg₀.1 hs', hD g₀ hg₀⟩
  let L : Mx k r →L[ℝ] Mx k r := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ s')
  have hL : ∀ x, L x = x * s' := fun _ => rfl
  refine ⟨L ⁻¹' U, fun x => F (L x), hU.preimage L.continuous, by simpa [hL] using hgU,
    hF.comp L.contDiff.contDiffOn (fun _ hx => hx), fun x hx hxG => ?_⟩
  have hx' : x * s' ∈ U := by rw [← hL]; exact hx
  show f (x * s') = F (L x)
  rw [hL]
  exact hfF _ hx' (glev_mul' hxG hs')
end Formalism.FourierDecayAlt.Q.TInvW

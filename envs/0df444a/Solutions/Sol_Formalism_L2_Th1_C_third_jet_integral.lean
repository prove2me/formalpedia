-- Prove2me | solution 1 for Formalism.L2.Th1.C.third_jet_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:15:22.373698+00:00
-- url     : https://prove2.me/submissions/a00f9f53-d8c3-4b4b-898a-aff20524f391

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ThirdJetIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_SigmaConstantAgrees
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntegralThirdInvariantDerivative
import Theorems.Thm_Formalism_L2_Th1_C_FormalGroupJetIntegrality_logDeriv
import Theorems.Thm_Formalism_L2_Th1_C_FormalGroupJetIntegrality_integral_third_invariant_derivative
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_intPS_Dinv
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_intPS_derivative
import Theorems.Thm_Formalism_LT_InvIntP_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open JetSubstitutionLemmas
namespace Formalism.L2.Th1.C
theorem _root_.solution : ThirdJetIntegral := by
  intro K _ _ R l linv ph hFr hF1
  have hl := FormalGroupJetIntegrality.logDeriv hFr.1 hFr.2.1
  have key : ∀ j : ℕ, IntPS R ((Dinv l)^[j + 3] ph) := by
    intro j
    induction j with
    | zero => exact FormalGroupJetIntegrality.integral_third_invariant_derivative hFr hF1
    | succ j ih =>
      rw [show j + 1 + 3 = (j + 3) + 1 by ring, Function.iterate_succ_apply']
      exact intPS_Dinv hl (intPS_derivative ih)
  refine ⟨key 0, fun i hi => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 3 := ⟨i - 3, by omega⟩
  unfold jet
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact key j 0
end Formalism.L2.Th1.C

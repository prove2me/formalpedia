-- Prove2me | solution 1 for Formalism.L2.Th1.C.jets_unramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:12:53.897206+00:00
-- url     : https://prove2.me/submissions/38a6036a-77da-4139-bc8f-ae09508487a7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ThirdJetIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_SigmaConstantAgrees
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntegralThirdInvariantDerivative
import Theorems.Thm_Formalism_L2_Th1_C_FormalGroupJetIntegrality_logDeriv
import Theorems.Thm_Formalism_L2_Th1_C_third_jet_integral
import Theorems.Thm_P2M_Formalism_L2_Th1_C_jetAdjoint__bce2b7401698
import Theorems.Thm_P2M_Formalism_L2_Th1_C_jetExp__59c42dc7203e
import Theorems.Thm_P2M_Formalism_L2_Th1_C_jetOne__d1e841762b79


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
namespace Formalism.L2.Th1.C
theorem _root_.solution : JetsUnramified := by
  intro K _ _ R l linv ph a b hFr hF1 hN h2 hAdj hinv hab
  have hl := FormalGroupJetIntegrality.logDeriv hFr.1 hFr.2.1
  have hj : ∀ i : ℕ, 1 ≤ i → jet l ph i ∈ R := by
    intro i hi
    rcases (by omega : i = 1 ∨ i = 2 ∨ 3 ≤ i) with rfl | rfl | h3
    · exact jetOne' K R l linv ph hFr.1 hl hFr.2.2 hN h2
    · have e := R.mul_mem hinv (jetAdjoint' K R l linv ph a b hFr.1 hFr.2.2 hAdj)
      rwa [← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.2 hab), one_mul] at e
    · exact (third_jet_integral K R l linv ph hFr hF1).2 i h3
  exact ⟨hj, jetExp' K R l linv ph hFr.1 hFr.2.2 hj⟩
end Formalism.L2.Th1.C

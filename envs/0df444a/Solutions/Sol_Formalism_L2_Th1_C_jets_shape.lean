-- Prove2me | solution 1 for Formalism.L2.Th1.C.jets_shape
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:01:15.321089+00:00
-- url     : https://prove2.me/submissions/f2fc9161-b7ec-4c52-b7e9-c39767bf30a4

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ThirdJetIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_SigmaConstantAgrees
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntegralThirdInvariantDerivative
import Theorems.Thm_Formalism_L2_Th1_C_FormalGroupJetIntegrality_logDeriv
import Theorems.Thm_Formalism_L2_Th1_C_third_jet_integral
import Theorems.Thm_P2M_Formalism_L2_Th1_C_jetAdjoint__bce2b7401698
import Theorems.Thm_P2M_Formalism_L2_Th1_C_jetExpShape__5793257a24c6
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
theorem _root_.solution : JetsShape := by
  intro K _ _ R l linv ph hFr hF1 hN h2
  have hl := FormalGroupJetIntegrality.logDeriv hFr.1 hFr.2.1
  refine ⟨jetExpShape' K R l linv ph hFr.1 hFr.2.2 (fun i hi hi2 => ?_),
    fun a b hAdj => jetAdjoint' K R l linv ph a b hFr.1 hFr.2.2 hAdj⟩
  rcases (by omega : i = 1 ∨ 3 ≤ i) with rfl | h3
  · exact jetOne' K R l linv ph hFr.1 hl hFr.2.2 hN h2
  · exact (third_jet_integral K R l linv ph hFr hF1).2 i h3
end Formalism.L2.Th1.C

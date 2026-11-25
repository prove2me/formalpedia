-- Prove2me | solution 1 for Formalism.L2.Th1.C.sum_two_units_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:14:47.20236+00:00
-- url     : https://prove2.me/submissions/135d748b-95f7-458a-8cdd-4803eade4189

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ThirdJetIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_SigmaConstantAgrees
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntegralThirdInvariantDerivative

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
theorem _root_.solution : SumTwoUnitsProd := by
  intro A B _ _ hA hB x
  obtain ⟨u1, v1, h1⟩ := hA x.1
  obtain ⟨u2, v2, h2⟩ := hB x.2
  exact ⟨MulEquiv.prodUnits.symm (u1, u2), MulEquiv.prodUnits.symm (v1, v2), Prod.ext h1 h2⟩
end Formalism.L2.Th1.C

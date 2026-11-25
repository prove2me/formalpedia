-- Prove2me | solution 1 for Formalism.L2.Th1.C.all_jets_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:48:58.246798+00:00
-- url     : https://prove2.me/submissions/038785f7-4d17-4a11-89f1-3fc7ad7f5f52

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SigmaConstantAgrees
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_UnitaryInverseIdentity
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_SigmaConstantAgrees
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
theorem _root_.solution : JetsAll := by
  intro K _ _ R l linv ph a b hl hu h0 h3 hN h2 hAdj hinv hab
  refine jetExp' K R l linv ph hl h0 ?_
  intro i hi
  rcases Nat.lt_or_ge i 3 with h | h
  · have : i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl
    · exact jetOne' K R l linv ph hl hu h0 hN h2
    · have e := R.mul_mem hinv (jetAdjoint' K R l linv ph a b hl h0 hAdj)
      rwa [← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.2 hab), one_mul] at e
  · exact h3 i h
end Formalism.L2.Th1.C

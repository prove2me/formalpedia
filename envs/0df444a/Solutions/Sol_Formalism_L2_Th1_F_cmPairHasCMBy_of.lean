-- Prove2me | solution 1 for Formalism.L2.Th1.F.cmPairHasCMBy_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:22:23.416408+00:00
-- url     : https://prove2.me/submissions/e5a03a64-3e39-4b43-946e-7648c3e16a9d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstIsogeny
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HasCMByIsogenyOf
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism.L2.Th1.CM (omegaK HasCMBy)
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
namespace Formalism.L2.Th1.F
theorem _root_.solution (h : CmStable) : CmPairHasCMBy := by
  intro a b c d ha hd hdisc hb
  obtain ⟨k, hk⟩ := hb
  subst hk
  have hst := h a (2 * k + 1) c d ha hd hdisc (-k) 1
  have heq : omegaK d = ((-k : ℤ) : ℂ) + ((1 : ℤ) : ℂ) * cmTheta (2 * k + 1) d := by
    simp only [omegaK, cmTheta]
    push_cast
    ring
  intro w hw
  rw [heq]
  exact hst w hw
end Formalism.L2.Th1.F

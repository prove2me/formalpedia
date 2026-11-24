-- Prove2me | solution 1 for Formalism.L2.Th1.F.hasCMByScale_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:22:24.162814+00:00
-- url     : https://prove2.me/submissions/f3c9ba8d-2cbc-4139-9ee4-0b416600ce85

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstIsogeny
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HasCMByIsogenyOf

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
theorem _root_.solution (h : Homogeneity) : HasCMByScale := by
  intro d L c hc hL w hw
  have hmem := (h L c hc).1
  rw [hmem] at hw ⊢
  rw [show c⁻¹ * (omegaK d * w) = omegaK d * (c⁻¹ * w) by ring]
  exact hL _ hw
end Formalism.L2.Th1.F

-- Prove2me | solution 1 for Formalism.L2.Th1.F.hasCMByIsogeny_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:38:40.899752+00:00
-- url     : https://prove2.me/submissions/2fd94481-3594-48a4-b122-2be10e9b2be1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstIsogeny
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HasCMByIsogenyOf
import Theorems.Thm_Formalism_L2_Th1_F_CmBy_ne_zero

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
theorem _root_.solution (hs : HasCMByStable) (he : KerRepsExist) (hc : KerRepsCard)
    (hf : IsogenyFormulaInstance) (h2 : QuasiPeriodConstIsogeny) : HasCMByIsogeny := by
  intro d L hL m n hmn hd
  have hα0 := CmBy.ne_zero d hd m n hmn
  obtain ⟨hms, hnorm⟩ := hs d L hL m n
  obtain ⟨S, hS⟩ := he L _ hα0 hms
  exact ⟨S, hS, (hc L _ S hα0 hms hS).trans hnorm, hf L _ S hα0 hms hS, h2 L _ S hα0 hms hS⟩
end Formalism.L2.Th1.F

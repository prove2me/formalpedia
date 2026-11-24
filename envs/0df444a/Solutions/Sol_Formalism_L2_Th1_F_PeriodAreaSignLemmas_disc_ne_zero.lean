-- Prove2me | solution 1 for Formalism.L2.Th1.F.PeriodAreaSignLemmas.disc_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:25:05.548014+00:00
-- url     : https://prove2.me/submissions/f05715ca-23a8-4796-9e29-94bf250e3cad

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_QuasiPeriodConstUniqueOf
import Theorems.Thm_Formalism_L2_Th1_F_PeriodAreaSignLemmas_det_ne_zero
import Theorems.Thm_Formalism_L2_Th1_F_PeriodAreaSignLemmas_disc_eq

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.PeriodAreaSignLemmas
namespace Formalism.L2.Th1.F.PeriodAreaSignLemmas
theorem _root_.solution (L : PeriodPair) : L.ω₁ * conj L.ω₂ - L.ω₂ * conj L.ω₁ ≠ 0 := by
  rw [disc_eq]
  have : (det L : ℂ) ≠ 0 := by exact_mod_cast det_ne_zero L
  simp [this]
end Formalism.L2.Th1.F.PeriodAreaSignLemmas

-- Prove2me | solution 1 for Formalism.L2.Th1.F.PeriodAreaSignLemmas.disc_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:38.575847+00:00
-- url     : https://prove2.me/submissions/2917e87d-412f-4a2c-acbb-d3ef41a7617d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_QuasiPeriodConstUniqueOf
import Theorems.Thm_Formalism_L2_Th1_F_PeriodAreaSignLemmas_det_eq

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
theorem _root_.solution (L : PeriodPair) :
    L.ω₁ * conj L.ω₂ - L.ω₂ * conj L.ω₁ = -(2 * Complex.I * (det L : ℂ)) := by
  rw [det_eq]
  apply Complex.ext
  · simp; ring
  · simp; ring
end Formalism.L2.Th1.F.PeriodAreaSignLemmas

-- Prove2me | solution 1 for Formalism.L2.Th1.E.torsion_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:24:00.674194+00:00
-- url     : https://prove2.me/submissions/3919a154-f3bc-4006-8f6e-88d266271cc0

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Taylor0ConstMul
import Theorems.Thm_Formalism_ELL_torsionIntegral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
namespace Formalism.L2.Th1.E
theorem _root_.solution : TorsionIntegral := by
  intro K _ _ inst W hW P N hN hNP hP
  obtain ⟨h1, h2, h3, h4, h6, hΔ⟩ := hW
  have e : inst = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  subst e
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => exact Formalism.ELL.torsionIntegral.{0} K W ⟨h1, h2, h3, h4, h6⟩ hΔ N hN x y h hNP
end Formalism.L2.Th1.E

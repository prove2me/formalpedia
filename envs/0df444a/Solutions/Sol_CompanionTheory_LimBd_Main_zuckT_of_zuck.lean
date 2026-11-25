-- Prove2me | solution 1 for CompanionTheory.LimBd.Main.zuckT_of_zuck
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:16:05.87073+00:00
-- url     : https://prove2.me/submissions/d6b395ea-56bf-42a3-88a5-af9ecbcdba52

import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_KFinSmooth
import Definitions.Def_Formalism_PeriodIntegrals_DSInfCharCap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_CoreDefs
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.Main
open Formalism.FourierDecayAlt PI.UpqRep Matrix
open scoped InnerProductSpace
namespace CompanionTheory.LimBd.Main
theorem _root_.solution (h : PI.ZuckTensor.Zuck) : ZuckT fun _ _ => 0 := by
  intro n ε μ H _ _ _ σ hμ hσ g hg hlt
  obtain ⟨X, -⟩ := h n ε μ H σ hμ hσ ⟨g, by simpa using hlt, hg⟩
  exact ⟨X⟩
end CompanionTheory.LimBd.Main

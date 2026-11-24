-- Prove2me | solution 1 for CompanionTheory.D.gk.HwAlg.word_nil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:55:10.344138+00:00
-- url     : https://prove2.me/submissions/47e57ab3-d36f-4491-b2e3-8551cd55afd1

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_EqSmulOfWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.FourierDecayAlt.Qr
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.HwAlg
variable {U : Type} [AddCommGroup U] [Module ℂ U] {n : ℕ}
namespace CompanionTheory.D.gk.HwAlg
theorem _root_.solution (F : Fin n → Fin n → Module.End ℂ U) : word F [] = 1 := rfl
end CompanionTheory.D.gk.HwAlg

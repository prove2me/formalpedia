-- Prove2me | solution 1 for CompanionTheory.WaveGrid.LimSh.one_mem_letters
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:09:26.257781+00:00
-- url     : https://prove2.me/submissions/09038c26-e981-45b1-84f5-95b819b339b4

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_LettersPoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.WaveGrid CompanionTheory.WaveGrid.LimSh
open Formalism.FourierDecayAlt Matrix CompanionTheory.LimBd.Main
variable {k r : ℕ}
namespace CompanionTheory.WaveGrid.LimSh
theorem _root_.solution : (1 : B.Mat k r → ℂ) ∈ Letters k r := Submodule.subset_span (Or.inl rfl)
end CompanionTheory.WaveGrid.LimSh

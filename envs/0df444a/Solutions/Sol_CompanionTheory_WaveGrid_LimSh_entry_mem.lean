-- Prove2me | solution 1 for CompanionTheory.WaveGrid.LimSh.entry_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:24:43.620446+00:00
-- url     : https://prove2.me/submissions/5e7f8c2b-390d-4480-b729-0b904760fde5

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
theorem _root_.solution (i j : Fin (2 * r + k + 1)) : (fun g : B.Mat k r => g i j) ∈ Letters k r :=
  Submodule.subset_span (Or.inr ⟨Pi.single j 1, Pi.single i 1, Or.inl fun g _ => by simp⟩)
end CompanionTheory.WaveGrid.LimSh

-- Prove2me | solution 1 for CompanionTheory.WaveGrid.LimSh.letters_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:26:14.074012+00:00
-- url     : https://prove2.me/submissions/528713d1-5b0d-41cf-81ae-c5c6c0ce697e

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_LettersPoly
import Theorems.Thm_CompanionTheory_WaveGrid_LimSh_one_mem_letters

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
theorem _root_.solution (a : ℕ) : Letters k r ^ a ≤ Letters k r ^ (a + 1) := by
  intro x hx
  rw [pow_succ, ← mul_one x]
  exact Submodule.mul_mem_mul hx one_mem_letters
end CompanionTheory.WaveGrid.LimSh

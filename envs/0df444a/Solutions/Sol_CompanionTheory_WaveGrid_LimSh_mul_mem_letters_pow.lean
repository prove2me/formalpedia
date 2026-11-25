-- Prove2me | solution 1 for CompanionTheory.WaveGrid.LimSh.mul_mem_letters_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:56:19.347801+00:00
-- url     : https://prove2.me/submissions/79d8e52b-d455-4017-a171-f3085f625b12

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
theorem _root_.solution {a d : ℕ} {x y : B.Mat k r → ℂ} (hx : x ∈ Letters k r ^ a) (hy : y ∈ Letters k r ^ d) :
    x * y ∈ Letters k r ^ (a + d) := by
  rw [pow_add]
  exact Submodule.mul_mem_mul hx hy
end CompanionTheory.WaveGrid.LimSh

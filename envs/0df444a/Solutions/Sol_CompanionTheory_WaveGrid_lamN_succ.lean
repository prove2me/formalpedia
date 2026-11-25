-- Prove2me | solution 1 for CompanionTheory.WaveGrid.lamN_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:08:53.044801+00:00
-- url     : https://prove2.me/submissions/ff491a90-51fc-47c1-8693-5aa831440203

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_PStarTie

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid
open Formalism.FourierDecayAlt Finset GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
namespace CompanionTheory.WaveGrid
theorem _root_.solution {n : ℕ} (lam : Fin n → ℝ) (s : Fin n) : lamN lam (s + 1) = lam s := by
  simp [lamN]
end CompanionTheory.WaveGrid

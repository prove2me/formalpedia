-- Prove2me | solution 1 for CompanionTheory.WaveGrid.half_le_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:33:53.046474+00:00
-- url     : https://prove2.me/submissions/b75315ca-5b59-4bf5-b702-e727388cbb26

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
theorem _root_.solution {x : ℝ} (m : ℤ) (hx : x = m + 1 / 2) (h : 0 < x) : 1 / 2 ≤ x := by
  have h1 : (-1 : ℝ) < m := by linarith
  have h2 : (0 : ℤ) ≤ m := by
    have : (-1 : ℤ) < m := by exact_mod_cast h1
    omega
  have h3 : (0 : ℝ) ≤ m := by exact_mod_cast h2
  linarith
end CompanionTheory.WaveGrid

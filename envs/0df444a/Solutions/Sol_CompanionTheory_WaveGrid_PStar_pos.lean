-- Prove2me | solution 1 for CompanionTheory.WaveGrid.PStar_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:19:25.468025+00:00
-- url     : https://prove2.me/submissions/c4188fbf-77ea-4a61-9498-2110cb11b3db

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
theorem _root_.solution {n : ℕ} (lam : Fin n → ℝ) {c : ℝ} (hc : 0 < c) (y : ℝ) : 0 < PStar lam c y :=
  Finset.prod_pos fun _ _ => add_pos_of_nonneg_of_pos (abs_nonneg _) hc
end CompanionTheory.WaveGrid

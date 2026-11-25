-- Prove2me | solution 1 for CompanionTheory.WaveGrid.Inhab.lamX_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:59:14.291103+00:00
-- url     : https://prove2.me/submissions/e44f4240-bba7-4c9f-b1ee-2d21dc494b6e

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_PStarTie
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_CfgTie
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqOfLamData

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid CompanionTheory.WaveGrid.Inhab
open Formalism.FourierDecayAlt Finset CompanionTheory.WaveGrid GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
namespace CompanionTheory.WaveGrid.Inhab
theorem _root_.solution (x : ℤ) (hx : 0 ≤ x) : StrictAnti (lamX x) := by
  have hx' : (0 : ℝ) ≤ x := by exact_mod_cast hx
  rw [Fin.strictAnti_iff_succ_lt]
  intro i
  fin_cases i <;> simp [lamX] <;> norm_num <;> linarith
end CompanionTheory.WaveGrid.Inhab

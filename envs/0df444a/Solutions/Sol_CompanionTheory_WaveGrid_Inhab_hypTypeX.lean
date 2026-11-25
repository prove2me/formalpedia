-- Prove2me | solution 1 for CompanionTheory.WaveGrid.Inhab.hypTypeX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:32:34.598713+00:00
-- url     : https://prove2.me/submissions/6f0f733d-bc4f-4783-94ef-0010a3974862

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_PStarTie
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_CfgTie
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqOfLamData
import Theorems.Thm_CompanionTheory_WaveGrid_Inhab_lamX_anti

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
theorem _root_.solution (x : ℤ) (hx : 0 ≤ x) (hx' : x ≤ 79) : HypType 3 0 (lamX x) uX 80 := by
  have hx0 : (0 : ℝ) ≤ x := by exact_mod_cast hx
  have hx1 : (x : ℝ) ≤ 79 := by exact_mod_cast hx'
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · intro i h1 h3
    interval_cases i
    · exact ⟨79, by simp [uX]; norm_num⟩
    · exact ⟨-1, by simp [uX]; norm_num⟩
    · exact ⟨-51, by simp [uX]; norm_num⟩
  · intro a b hab
    apply lamX_anti x hx
    rw [Fin.lt_def] at hab ⊢
    simpa using hab
  · intro i
    fin_cases i <;> simp [lamX, uX] <;> norm_num <;> first | (refine ⟨?_, ?_⟩ <;> linarith) | linarith
  · intro i h1 h3
    interval_cases i <;> simp [uX] <;> norm_num
end CompanionTheory.WaveGrid.Inhab

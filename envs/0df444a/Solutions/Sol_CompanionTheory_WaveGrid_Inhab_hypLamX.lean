-- Prove2me | solution 1 for CompanionTheory.WaveGrid.Inhab.hypLamX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:34:32.813945+00:00
-- url     : https://prove2.me/submissions/62b4f3c1-c54c-454a-a009-a670ab4c14a9

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
theorem _root_.solution (x : ℤ) (hx : 0 ≤ x) (hx' : x ≤ 79) : HypLam 3 0 (lamX x) 10 20 80 := by
  have hx0 : (0 : ℝ) ≤ x := by exact_mod_cast hx
  have hx1 : (x : ℝ) ≤ 79 := by exact_mod_cast hx'
  refine ⟨⟨lamX_anti x hx, ?_⟩, ?_, by norm_num, by norm_num, ?_, by norm_num, by norm_num, ?_⟩
  · intro a
    fin_cases a
    · exact ⟨x - 1, by simp [lamX]; push_cast; ring⟩
    · exact ⟨-41, by simp [lamX]; norm_num⟩
    · exact ⟨-61, by simp [lamX]; norm_num⟩
    · exact ⟨-81, by simp [lamX]; norm_num⟩
  · intro s
    rw [abs_le]
    fin_cases s <;> simp [lamX] <;> constructor <;> linarith
  · have he := Real.exp_one_lt_d9
    push_cast
    linarith
  · intro s t hst
    fin_cases s <;> fin_cases t <;> simp at hst <;> simp [lamX] <;> linarith
end CompanionTheory.WaveGrid.Inhab

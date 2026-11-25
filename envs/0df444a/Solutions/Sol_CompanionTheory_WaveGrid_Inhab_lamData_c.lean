-- Prove2me | solution 1 for CompanionTheory.WaveGrid.Inhab.lamData_c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:49:20.050872+00:00
-- url     : https://prove2.me/submissions/f08f745c-0b9b-491d-a68e-a997339be628

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_PStarTie
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_CfgTie
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqOfLamData
import Theorems.Thm_P2M_CompanionTheory_WaveGrid_Inhab_cfg__ok_26ff93befe17
import Theorems.Thm_CompanionTheory_WaveGrid_lamData_cfg


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
theorem _root_.solution : LamData Pc cfg₁.lam 10 (4 * cfg₁.Del) 401 := by
  refine lamData_cfg cfg₁ 0 rfl cfg₁_ok 1 1 (fun _ => 0) (fun i => if i = 1 then 1 else 0) (fun _ => Or.inl rfl)
    (fun i => by by_cases h : i = 1 <;> simp [h]) 10 401 (by norm_num) (by norm_num [cfg₁, cfg₀])
    (by norm_num [cfg₁, cfg₀]) ?_
  intro j _ hj2
  simp [cfg₁, cfg₀] at hj2 ⊢
  have : (j : ℝ) ≤ 2 := by exact_mod_cast hj2
  linarith
end CompanionTheory.WaveGrid.Inhab

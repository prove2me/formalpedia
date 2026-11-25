-- Prove2me | solution 1 for CompanionTheory.WaveGrid.Inhab.Pc_OK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:33:06.876302+00:00
-- url     : https://prove2.me/submissions/0d4d818c-3b48-41f9-b9f8-dd2dc2cf21b6

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
theorem _root_.solution : Pc.OK := by
  refine ⟨by norm_num [Pc, cfgPar, cfg₁, cfg₀], by norm_num [Pc, cfgPar], by norm_num [Pc, cfgPar], ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i ∈ Finset.Icc 1 4 := hi
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hi'
    interval_cases i
    · exact ⟨0, by simp⟩
    · exact ⟨-281, by simp [Pc, cfgPar, Sz.Cfg.u, Sz.Cfg.v, Sz.Cfg.ulast, cfg₁, cfg₀]; norm_num⟩
    · exact ⟨-341, by simp [Pc, cfgPar, Sz.Cfg.u, Sz.Cfg.v, Sz.Cfg.ulast, cfg₁, cfg₀]; norm_num⟩
    · exact ⟨-401, by simp [Pc, cfgPar, Sz.Cfg.u, Sz.Cfg.v, Sz.Cfg.ulast, cfg₁, cfg₀]; norm_num⟩
  · intro i hi
    have hi' : i ∈ Finset.Icc 1 4 := hi
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hi'
    interval_cases i
    · exact ⟨0, by simp [Pc, cfgPar, Sz.Cfg.u]⟩
    · exact ⟨-296, by simp [Pc, cfgPar, Sz.Cfg.u, Sz.Cfg.v, Sz.Cfg.ulast, cfg₁, cfg₀]; norm_num⟩
    · exact ⟨-341, by simp [Pc, cfgPar, Sz.Cfg.u, Sz.Cfg.v, Sz.Cfg.ulast, cfg₁, cfg₀]; norm_num⟩
    · exact ⟨-401, by simp [Pc, cfgPar, Sz.Cfg.u, Sz.Cfg.v, Sz.Cfg.ulast, cfg₁, cfg₀]; norm_num⟩
  · intro i hi
    have hi' : i ∈ Finset.Icc 1 3 := hi
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hi'
    interval_cases i <;>
      simp [M.Par.lo, M.Par.hi, Pc, cfgPar, Sz.Cfg.u, Sz.Cfg.v, Sz.Cfg.ulast, cfg₁, cfg₀] <;> norm_num
end CompanionTheory.WaveGrid.Inhab

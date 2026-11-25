-- Prove2me | solution 1 for CompanionTheory.WaveGrid.lamData_cfg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:54:58.548206+00:00
-- url     : https://prove2.me/submissions/f33957d1-6831-45dc-a530-94a298a3a865

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_CfgTie
import Theorems.Thm_CompanionTheory_WaveGrid_cfg_v_step
import Theorems.Thm_CompanionTheory_WaveGrid_cfg_v_mem
import Theorems.Thm_CompanionTheory_WaveGrid_cfg_b_pos
import Theorems.Thm_CompanionTheory_WaveGrid_cfg_inter
import Theorems.Thm_CompanionTheory_WaveGrid_cfg_u_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid
open Formalism.FourierDecayAlt Finset
variable (c : Sz.Cfg)
namespace CompanionTheory.WaveGrid
theorem _root_.solution (r : ℕ) (hm : c.m = 2 * r + 2) (hok : c.Ok) (T T' : ℝ) (de de' : ℕ → ℝ)
    (hde : ∀ i, de i = 0 ∨ de i = 1) (hde' : ∀ i, de' i = 0 ∨ de' i = 1) (cs b : ℝ) (hc0 : 0 < cs)
    (hc : 1 + cs ≤ 4 * c.Del) (ha : c.a ≤ b) (hb : ∀ j, 1 ≤ j → j ≤ c.m → c.b j ≤ b) :
    LamData (cfgPar c r T T' de de') c.lam cs (4 * c.Del) b := by
  have hk4 : 4 ≤ c.k := hok.hk
  have hD : (1:ℝ) ≤ c.Del := hok.hDel
  have hk' : (4:ℝ) ≤ c.k := by exact_mod_cast hk4
  have hprod : 16 * c.Del ≤ 4 * c.k * c.Del := by
    nlinarith [mul_nonneg (sub_nonneg.2 hk') (by linarith : (0:ℝ) ≤ c.Del)]
  have hkD : (c.k:ℝ) ≤ 4 * c.k * c.Del := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ c.k) (sub_nonneg.2 hD)]
  have hv1 : c.vlast ≤ c.v 1 := (cfg_v_mem c hok 1 le_rfl (by omega)).1
  have hv0 := hok.hv0
  have hav := hok.ha
  have hbpos := cfg_b_pos c hok
  refine ⟨hc0, hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · show (c.k:ℝ) ≤ b
    linarith
  · linarith
  · intro s hs1 hs2
    change s ≤ c.k + 2 * r + 1 at hs2
    rw [Sz.Cfg.lam]
    split_ifs with hsk
    · have := cfg_v_mem c hok s hs1 (by omega)
      rw [abs_le]
      constructor <;> linarith [this.1, this.2]
    · have hj1 : 1 ≤ s + 1 - c.k := by omega
      have hj2 : s + 1 - c.k ≤ c.m := by omega
      have h1 := hbpos _ hj1 hj2
      have h2 := hb _ hj1 hj2
      rw [abs_neg, abs_of_pos (by linarith)]
      exact h2
  · intro s hs1 hs2
    change s + 1 ≤ c.k - 1 at hs2
    rw [Sz.Cfg.lam, Sz.Cfg.lam, if_pos (by omega), if_pos (by omega)]
    have := cfg_v_step c s
    linarith
  · intro s hs1 hs2
    exact ⟨cfg_inter c hok de hde s hs1 hs2, cfg_inter c hok de' hde' s hs1 hs2⟩
  · intro i hi1 hi2
    have hb1 := hb 1 le_rfl (by omega)
    exact ⟨cfg_u_le c hok de hde b ha hb1 i hi1 hi2, cfg_u_le c hok de' hde' b ha hb1 i hi1 hi2⟩
end CompanionTheory.WaveGrid

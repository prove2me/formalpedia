-- Prove2me | solution 1 for CompanionTheory.WaveGrid.cfg_u_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:32:01.413911+00:00
-- url     : https://prove2.me/submissions/00eb19c9-737c-4b64-aa30-e4470e7ea115

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_CfgTie
import Theorems.Thm_CompanionTheory_WaveGrid_cfg_v_mem

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
theorem _root_.solution (hok : c.Ok) (de : ℕ → ℝ) (hde : ∀ i, de i = 0 ∨ de i = 1) (b : ℝ) (ha : c.a ≤ b)
    (hb1 : c.b 1 ≤ b) (i : ℕ) (hi1 : 1 ≤ i) (hik : i ≤ c.k) : |c.u de i| ≤ b := by
  have hk4 : 4 ≤ c.k := hok.hk
  have hD : (1:ℝ) ≤ c.Del := hok.hDel
  have hk' : (4:ℝ) ≤ c.k := by exact_mod_cast hk4
  have hprod : 16 * c.Del ≤ 4 * c.k * c.Del := by
    nlinarith [mul_nonneg (sub_nonneg.2 hk') (by linarith : (0:ℝ) ≤ c.Del)]
  have hv1 : c.vlast ≤ c.v 1 := (cfg_v_mem c hok 1 le_rfl (by omega)).1
  have hv0 := hok.hv0
  have hav := hok.ha
  have hb1 := hok.hb1
  rw [Sz.Cfg.u, abs_le]
  split_ifs with h1 h2
  · constructor <;> linarith
  · rw [Sz.Cfg.ulast]
    split_ifs with ht
    · obtain ⟨h3, h4⟩ := hok.htop ht
      constructor <;> linarith
    · constructor <;> linarith
  · have hm := cfg_v_mem c hok (i - 1) (by omega) (by omega)
    rcases hde (i - 1) with h0 | h0 <;> rw [h0] <;> constructor <;> linarith [hm.1, hm.2]
end CompanionTheory.WaveGrid

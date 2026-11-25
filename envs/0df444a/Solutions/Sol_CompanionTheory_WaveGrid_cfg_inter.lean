-- Prove2me | solution 1 for CompanionTheory.WaveGrid.cfg_inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:36:52.403006+00:00
-- url     : https://prove2.me/submissions/7c545ec9-bd38-4eba-8b2f-cefcc06842f5

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_CfgTie
import Theorems.Thm_CompanionTheory_WaveGrid_cfg_v_step
import Theorems.Thm_CompanionTheory_WaveGrid_cfg_v_last

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
theorem _root_.solution (hok : c.Ok) (de : ℕ → ℝ) (hde : ∀ i, de i = 0 ∨ de i = 1) (s : ℕ) (hs1 : 1 ≤ s)
    (hsk : s ≤ c.k - 1) : c.lam s + 1 / 2 ≤ c.u de s ∧ c.u de (s + 1) ≤ c.lam s - 1 / 2 := by
  have hk4 : 4 ≤ c.k := hok.hk
  have hD : (1:ℝ) ≤ c.Del := hok.hDel
  have hk' : (4:ℝ) ≤ c.k := by exact_mod_cast hk4
  have hlam : c.lam s = c.v s := by
    rw [Sz.Cfg.lam, if_pos (by omega)]
  rw [hlam]
  constructor
  · rcases Nat.lt_or_ge s 2 with h | h
    · have hs : s = 1 := by omega
      subst hs
      rw [Sz.Cfg.u, if_pos rfl]
      have := hok.ha
      nlinarith [mul_nonneg (sub_nonneg.2 hk') (sub_nonneg.2 hD)]
    · rw [Sz.Cfg.u, if_neg (by omega), if_neg (by omega)]
      have hstep := cfg_v_step c (s - 1)
      rw [Nat.sub_add_cancel hs1] at hstep
      rcases hde (s - 1) with h0 | h0 <;> rw [h0] <;> linarith
  · rw [Sz.Cfg.u, if_neg (by omega)]
    by_cases hks : s + 1 = c.k
    · rw [if_pos hks, Sz.Cfg.ulast]
      have hv : c.v s = c.vlast := by
        have := cfg_v_last c (by omega : 1 ≤ c.k)
        rw [show s = c.k - 1 by omega]
        exact this
      rw [hv]
      split_ifs with ht
      · obtain ⟨h1, _⟩ := hok.htop ht
        have := hok.hb1
        have := hok.hv0
        linarith
      · linarith
    · rw [if_neg hks, Nat.add_sub_cancel]
      rcases hde s with h0 | h0 <;> rw [h0] <;> linarith
end CompanionTheory.WaveGrid

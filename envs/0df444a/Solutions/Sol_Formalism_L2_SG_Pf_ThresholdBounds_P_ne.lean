-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ThresholdBounds.P_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:27:20.053434+00:00
-- url     : https://prove2.me/submissions/6d70231b-b163-4c55-8422-79c00a55060b

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ThresholdBounds
import Theorems.Thm_Formalism_L2_SG_Pf_ThresholdBounds_v_sub
import Theorems.Thm_Formalism_L2_SG_Pf_ThresholdBounds_b_one_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace Formalism.L2.SG.Pf.ThresholdBounds
open Formalism.FourierDecayAlt
variable (c : Sz.Cfg)
private theorem v_eq_vlast_add_four_mul_Del (i : ℕ) : c.v i = c.vlast + 4 * c.Del * ((c.k : ℝ) - 1 - (i : ℝ)) := rfl
end Formalism.L2.SG.Pf.ThresholdBounds
end
end

set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ThresholdBounds
open Formalism.FourierDecayAlt
variable (c : Sz.Cfg)
namespace Formalism.L2.SG.Pf.ThresholdBounds
theorem _root_.solution (hOk : c.Ok) (hb1 : 40 * (c.m : ℝ) * c.k * c.Del ≤ c.b 1) {l : ℕ} (hl : l + 1 ≤ c.k) {t : ℝ}
    (ht0 : 0 < t) (ht4 : t < 4) : c.P (t - c.v l) ≠ 0 := by
  have hk4 : (4 : ℝ) ≤ c.k := by exact_mod_cast hOk.hk
  have hm2 : (2 : ℝ) ≤ c.m := by exact_mod_cast hOk.hm
  have hD := hOk.hDel
  have hv0 := hOk.hv0
  have hlk : (l : ℝ) + 1 ≤ c.k := by exact_mod_cast hl
  have hvl : c.vlast ≤ c.v l := by
    rw [v_eq_vlast_add_four_mul_Del c l]
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * c.Del) (by linarith : (0 : ℝ) ≤ (c.k : ℝ) - 1 - l)
    linarith
  have hmk : (8 : ℝ) * c.Del ≤ (c.m : ℝ) * c.k * c.Del := by
    have h8 : (8 : ℝ) ≤ (c.m : ℝ) * c.k := by nlinarith
    exact mul_le_mul_of_nonneg_right h8 (by linarith)
  show (∏ s ∈ Icc 1 (c.k + c.m - 1), ((t - c.v l) + c.lam s)) ≠ 0
  rw [Finset.prod_ne_zero_iff]
  intro s hs
  rw [Finset.mem_Icc] at hs
  by_cases hsk : s < c.k
  · have hlam : c.lam s = c.v s := by simp [Formalism.FourierDecayAlt.Sz.Cfg.lam, hsk]
    rw [hlam]
    have e := v_sub c s l
    rcases lt_trichotomy s l with h | rfl | h
    · have h' : (s : ℝ) + 1 ≤ l := by exact_mod_cast h
      have : 4 * c.Del * 1 ≤ 4 * c.Del * ((l : ℝ) - s) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      apply ne_of_gt; linarith
    · apply ne_of_gt; linarith
    · have h' : (l : ℝ) + 1 ≤ s := by exact_mod_cast h
      have : 4 * c.Del * ((l : ℝ) - s) ≤ 4 * c.Del * (-1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      apply ne_of_lt; linarith
  · have hlam : c.lam s = -c.b (s + 1 - c.k) := by simp [Formalism.FourierDecayAlt.Sz.Cfg.lam, hsk]
    rw [hlam]
    have hj1 : 1 ≤ s + 1 - c.k := by omega
    have hjm : s + 1 - c.k ≤ c.m := by have := hOk.hm; omega
    have hbj := b_one_le c hOk _ hj1 hjm
    apply ne_of_lt; linarith
end Formalism.L2.SG.Pf.ThresholdBounds

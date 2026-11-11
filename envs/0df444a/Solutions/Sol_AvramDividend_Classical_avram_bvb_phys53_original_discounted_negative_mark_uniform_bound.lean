-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys53_original_discounted_negative_mark_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T15:35:39.023582+00:00
-- url     : https://prove2.me/submissions/25b088b4-ee32-411f-8a98-e74423625f19

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Topology.Defs.Filter
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys44_original_cap_reward_bounded_below_cap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A fixed finite reserve cap controls every discounted negative-mark payoff. -/
theorem solution
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (t u z : ℝ), 0 ≤ t → 0 ≤ u → ENNReal.ofReal u ≤ C → z < 0 →
        |Real.exp (-(q * t)) * (w (u + z) - w u)| ≤ K := by
  obtain ⟨R, hR, hBound⟩ :=
    avram_bvb_phys44_original_cap_reward_bounded_below_cap
      w hw_cont hw_neg C.toReal ENNReal.toReal_nonneg
  refine ⟨2 * R, mul_nonneg (by norm_num) hR, ?_⟩
  intro t u z ht hu huC hz
  have huCap : u ≤ C.toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hFinite).mp huC
  have huzCap : u + z ≤ C.toReal := by linarith
  have huW := hBound u huCap
  have huzW := hBound (u + z) huzCap
  have hReward : |w (u + z) - w u| ≤ R + R := by
    calc
      |w (u + z) - w u| ≤ |w (u + z)| + |w u| := by
        simpa using (abs_sub_le (w (u + z)) 0 (w u))
      _ ≤ R + R := add_le_add huzW huW
  have hDisc : Real.exp (-(q * t)) ≤ 1 := by
    calc
      Real.exp (-(q * t)) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg hq ht))
      _ = 1 := Real.exp_zero
  calc
    |Real.exp (-(q * t)) * (w (u + z) - w u)| =
        Real.exp (-(q * t)) * |w (u + z) - w u| := by
          rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    _ ≤ Real.exp (-(q * t)) * (R + R) :=
      mul_le_mul_of_nonneg_left hReward (Real.exp_nonneg _)
    _ ≤ 1 * (R + R) :=
      mul_le_mul_of_nonneg_right hDisc (add_nonneg hR hR)
    _ = 2 * R := by ring

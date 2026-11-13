-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_topcap_compact_discounted_negative_mark_kernel_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:08:02.369483+00:00
-- url     : https://prove2.me/submissions/5aa5c7cd-d552-4e3f-9a65-43360e5d5864

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger63_compact_continuous_value_finite_lower_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory
noncomputable section

theorem solution
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (B q : ℝ) (hB : 0 ≤ B) (hq : 0 ≤ q) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (t b z : ℝ), 0 ≤ t → 0 ≤ b → b ≤ B → z < 0 →
        |Real.exp (-(q * t)) * (w (b + z) - w b)| ≤ K := by
  have hsubset : Icc (0 : ℝ) B ⊆ Ici (0 : ℝ) := by
    intro y hy
    exact hy.1
  have hwI : ContinuousOn w (Icc (0 : ℝ) B) :=
    hw.mono hsubset
  obtain ⟨L, hL0, hL⟩ :=
    AvramDividend.Classical.avram_gledger63_compact_continuous_value_finite_lower_bound
      0 B hB w hwI
  obtain ⟨U, hU0, hU⟩ :=
    AvramDividend.Classical.avram_gledger63_compact_continuous_value_finite_lower_bound
      0 B hB (fun y : ℝ => -w y) hwI.neg
  have hval : ∀ y : ℝ, 0 ≤ y → y ≤ B → |w y| ≤ L + U := by
    intro y hy0 hyB
    have hlo := hL y hy0 hyB
    have hhi := hU y hy0 hyB
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  refine ⟨(L + U) + (L + U), by positivity, ?_⟩
  intro t b z ht hb0 hbB hz
  have hraw : |w (b + z) - w b| ≤ (L + U) + (L + U) := by
    by_cases hneg : b + z < 0
    · rw [hw_neg (b + z) hneg]
      have hb := hval b hb0 hbB
      simpa only [zero_sub, abs_neg] using
        le_trans hb (by linarith : L + U ≤ (L + U) + (L + U))
    · have hz0 : 0 ≤ b + z := le_of_not_gt hneg
      have hzB : b + z ≤ B := by linarith
      calc
        |w (b + z) - w b| ≤ |w (b + z)| + |w b| := by
          simpa only [sub_zero, zero_sub, abs_neg] using
            (abs_sub_le (w (b + z)) (0 : ℝ) (w b))
        _ ≤ (L + U) + (L + U) :=
          add_le_add (hval (b + z) hz0 hzB) (hval b hb0 hbB)
  have hexp : Real.exp (-(q * t)) ≤ (1 : ℝ) := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg hq ht]
  calc
    |Real.exp (-(q * t)) * (w (b + z) - w b)| =
        Real.exp (-(q * t)) * |w (b + z) - w b| := by
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ 1 * |w (b + z) - w b| :=
      mul_le_mul_of_nonneg_right hexp (abs_nonneg _)
    _ = |w (b + z) - w b| := one_mul _
    _ ≤ (L + U) + (L + U) := hraw

-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin27_original_negative_mark_reward_increment_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T14:40:39.702896+00:00
-- url     : https://prove2.me/submissions/9564c257-0ac8-4800-a6cd-baed781a83ac

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gauss_finitec2_gradient_growth_to_cap
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_original_reward_nonnegative_below_interior
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t < 0, w t = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {t : ℝ | 0 < t ∧ ENNReal.ofReal t < C})
    (hw_grad : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t < C → 1 ≤ deriv w t)
    (y z : ℝ) (hy : 0 < y)
    (hyC : ENNReal.ofReal y < C) (hz : z < 0) :
    |w (y + z) - w y| ≤ w y := by
  have hmon : ∀ a : ℝ, 0 ≤ a → a ≤ y → w a ≤ w y := by
    intro a ha hay
    rcases eq_or_lt_of_le hay with heq | hlt
    · rw [heq]
    · have hSubset : Ioo a y ⊆
          {t : ℝ | 0 < t ∧ ENNReal.ofReal t < C} := by
        intro t ht
        exact ⟨lt_of_le_of_lt ha ht.1,
          (ENNReal.ofReal_le_ofReal (le_of_lt ht.2)).trans_lt hyC⟩
      have hC1 : ContDiffOn ℝ 1 w (Ioo a y) :=
        (hw_smooth.mono hSubset).of_le (by norm_num)
      have hDeriv : ∀ t ∈ Ioo a y,
          HasDerivAt w (deriv w t) t := by
        intro t ht
        exact ((hC1.differentiableOn_one t ht).differentiableAt
          (isOpen_Ioo.mem_nhds ht)).hasDerivAt
      have hCont : ContinuousOn w (Icc a y) :=
        hw_cont.mono (by
          intro t ht
          exact le_trans ha ht.1)
      have hGrad : ∀ t ∈ Ioo a y, 1 ≤ deriv w t := by
        intro t ht
        exact hw_grad t (hSubset ht).1 (hSubset ht).2
      have hg := avram_gauss_finitec2_gradient_growth_to_cap
        w a y hlt hCont hDeriv hGrad
      have hval := hg a ⟨le_refl a, le_of_lt hlt⟩
      linarith
  have hwy : 0 ≤ w y := by
    have h0 := hmon 0 (le_refl 0) (le_of_lt hy)
    linarith
  have hlanding : 0 ≤ w (y + z) :=
    avram_mix_fin26_original_reward_nonnegative_below_interior
      C hC w hw0 hw_cont hw_neg hw_smooth hw_grad y hy hyC
      (y + z) (by linarith)
  have hlanding_le : w (y + z) ≤ w y := by
    rcases le_total (y + z) 0 with hn | hp
    · rcases lt_or_eq_of_le hn with hneg | heq
      · rw [hw_neg (y + z) hneg]
        exact hwy
      · rw [heq]
        exact hmon 0 (le_refl 0) (le_of_lt hy)
    · exact hmon (y + z) hp (by linarith)
  calc
    |w (y + z) - w y| = -(w (y + z) - w y) :=
      abs_of_nonpos (sub_nonpos.mpr hlanding_le)
    _ = w y - w (y + z) := by ring
    _ ≤ w y := by linarith

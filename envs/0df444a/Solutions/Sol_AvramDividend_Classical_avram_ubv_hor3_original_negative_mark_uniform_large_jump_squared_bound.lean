-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_negative_mark_uniform_large_jump_squared_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:01:08.909204+00:00
-- url     : https://prove2.me/submissions/d7c43503-296c-44f5-b047-499fcde003ca

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_tail_global_value_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ u ∈ Icc δ K, ∀ z : ℝ, z < 0 →
        (w (u + z) - w u) ^ 2 ≤ M := by
  have hK : 0 ≤ K := le_trans (le_of_lt hδ) hδK
  obtain ⟨A, hA, hBound⟩ :=
    avram_p4_f3_original_negative_tail_global_value_bound
      w hw_cont hw_neg K hK
  refine ⟨(2 * A) ^ 2, sq_nonneg _, ?_⟩
  intro u hu z hz
  have huz : u + z ≤ K := by
    have huK : u ≤ K := hu.2
    linarith
  have hAu : |w u| ≤ A := hBound u hu.2
  have hAuz : |w (u + z)| ≤ A := hBound (u + z) huz
  have hAbs : |w (u + z) - w u| ≤ 2 * A := by
    calc
      |w (u + z) - w u| ≤ |w (u + z)| + |w u| := abs_sub _ _
      _ ≤ A + A := add_le_add hAuz hAu
      _ = 2 * A := by ring
  have hPlus : 0 ≤ 2 * A + |w (u + z) - w u| :=
    add_nonneg (by positivity) (abs_nonneg _)
  have hMul : 0 ≤
      (2 * A - |w (u + z) - w u|) *
        (2 * A + |w (u + z) - w u|) :=
    mul_nonneg (sub_nonneg.mpr hAbs) hPlus
  have hsq : |w (u + z) - w u| ^ 2 =
      (w (u + z) - w u) ^ 2 := by
    exact sq_abs _
  nlinarith

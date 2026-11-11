-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin26_original_reward_upper_by_interior_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T14:01:27.989551+00:00
-- url     : https://prove2.me/submissions/efbf700f-cfef-4e38-aa63-5e885aab0fcc

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gauss_finitec2_gradient_growth_to_cap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (u v : ℝ) (hu : 0 < u) (huv : u < v)
    (hvC : ENNReal.ofReal v < C) :
    ∀ y ∈ Ico u v, w y ≤ w v := by
  have hSubset : Ioo u v ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy
    exact ⟨lt_trans hu hy.1,
      (ENNReal.ofReal_le_ofReal (le_of_lt hy.2)).trans_lt hvC⟩
  have hC1 : ContDiffOn ℝ 1 w (Ioo u v) :=
    (hw_smooth.mono hSubset).of_le (by norm_num)
  have hDeriv : ∀ y ∈ Ioo u v, HasDerivAt w (deriv w y) y := by
    intro y hy
    have hd : DifferentiableAt ℝ w y :=
      (hC1.differentiableOn_one y hy).differentiableAt
        (isOpen_Ioo.mem_nhds hy)
    exact hd.hasDerivAt
  have hCont : ContinuousOn w (Icc u v) :=
    hw_cont.mono (by
      intro y hy
      exact le_trans (le_of_lt hu) hy.1)
  have hGrad : ∀ y ∈ Ioo u v, 1 ≤ deriv w y := by
    intro y hy
    exact hw_grad y (hSubset hy).1 (hSubset hy).2
  have hg := avram_gauss_finitec2_gradient_growth_to_cap
    w u v huv hCont hDeriv hGrad
  intro y hy
  have hcap : y ∈ Icc u v := ⟨hy.1, le_of_lt hy.2⟩
  have hgrowth := hg y hcap
  have hdelta : 0 ≤ v - y := sub_nonneg.mpr hcap.2
  linarith

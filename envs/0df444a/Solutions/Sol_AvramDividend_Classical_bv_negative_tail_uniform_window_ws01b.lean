-- Prove2me | solution 1 for AvramDividend.Classical.bv_negative_tail_uniform_window_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T23:35:15.714395+00:00
-- url     : https://prove2.me/submissions/40d786b3-6590-4785-b8de-f6b548c316eb

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_negative_tail_continuous_of_standing_bv

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (δ a : ℝ) (hδ : 0 < δ) (hδa : 2 * δ ≤ a) :
    ∀ η : ℝ, 0 < η →
      ∃ ε : ℝ, 0 < ε ∧
        ∀ x ∈ Icc (2 * δ) a, ∀ s : ℝ,
          0 ≤ s → s ≤ ε →
          |X.ν.real (Iic (-(x - s))) -
            X.ν.real (Iic (-x))| < η := by
  intro η hη
  have hδ' : 0 < δ := hδ
  have hcont := AvramDividend.Classical.levy_negative_tail_continuous_of_standing_bv X hX hBV
  have hsub : Icc δ a ⊆ Ioi (0 : ℝ) := fun y hy => lt_of_lt_of_le hδ hy.1
  have huc : UniformContinuousOn (fun r : ℝ => X.ν.real (Iic (-r))) (Icc δ a) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (hcont.mono hsub)
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨d, hd, hdist⟩ := huc η hη
  refine ⟨min (d / 2) δ, lt_min (by linarith) hδ, ?_⟩
  intro x hx s hs0 hs
  have hs1 : s ≤ d / 2 := le_trans hs (min_le_left _ _)
  have hs2 : s ≤ δ := le_trans hs (min_le_right _ _)
  have hxm : x - s ∈ Icc δ a := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hxx : x ∈ Icc δ a := ⟨by linarith [hx.1], hx.2⟩
  have h := hdist (x - s) hxm x hxx (by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  rwa [Real.dist_eq] at h

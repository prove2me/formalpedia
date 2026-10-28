-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_positive_discount_C1_from_zero_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:22:55.299991+00:00
-- url     : https://prove2.me/submissions/9acfe728-36d9-4df6-aacd-648780fec6ba

import Theorems.Thm_AvramDividend_Classical_unbounded_psi_two_discounts_common_tail
import Theorems.Thm_AvramDividend_Classical_unbounded_positive_discount_C1_of_zero_discount_C1
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (W₀ : ℝ → ℝ) (hW₀ : IsScaleFunction X 0 W₀)
    (hW₀C1 : ContDiffOn ℝ 1 W₀ (Ioi (0 : ℝ)))
    (q : ℝ) (hq : 0 < q)
    (Wq : ℝ → ℝ) (hWq : IsScaleFunction X q Wq) :
    ContDiffOn ℝ 1 Wq (Ioi (0 : ℝ)) := by
  obtain ⟨b, hb0, hb⟩ :=
    unbounded_psi_two_discounts_common_tail X hnbv 0 q (by norm_num) (le_of_lt hq)
  have hθ : 0 ≤ b + 1 := by linarith
  have hbθ : b < b + 1 := by linarith
  have hqθ : q < X.ψ (b + 1) := (hb (b + 1) hbθ).2.2
  exact unbounded_positive_discount_C1_of_zero_discount_C1
    X hnbv W₀ hW₀ hW₀C1 q hq Wq hWq (b + 1) hθ hqθ

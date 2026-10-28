-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_C1_zero_iff_positive_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:37:16.692338+00:00
-- url     : https://prove2.me/submissions/23dec9ea-a121-4b4d-b48e-80f1158c710a

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_psi_two_discounts_common_tail
import Theorems.Thm_AvramDividend_Classical_unbounded_positive_discount_C1_from_zero_unconditional
import Theorems.Thm_AvramDividend_Classical_unbounded_zero_discount_C1_of_positive_discount_C1
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
    (q : ℝ) (hq : 0 < q)
    (Wq : ℝ → ℝ) (hWq : IsScaleFunction X q Wq) :
    ContDiffOn ℝ 1 W₀ (Ioi (0 : ℝ)) ↔
    ContDiffOn ℝ 1 Wq (Ioi (0 : ℝ)) := by
  constructor
  · intro hC0
    exact unbounded_positive_discount_C1_from_zero_unconditional
      X hnbv W₀ hW₀ hC0 q hq Wq hWq
  · intro hCq
    obtain ⟨b, hb0, hb⟩ :=
      unbounded_psi_two_discounts_common_tail X hnbv 0 q (by norm_num) (le_of_lt hq)
    have hθ : 0 ≤ b + 1 := by linarith
    have hbθ : b < b + 1 := by linarith
    have hqθ : q < X.ψ (b + 1) := (hb (b + 1) hbθ).2.2
    exact unbounded_zero_discount_C1_of_positive_discount_C1
      X hnbv W₀ hW₀ q hq Wq hWq hCq (b + 1) hθ hqθ

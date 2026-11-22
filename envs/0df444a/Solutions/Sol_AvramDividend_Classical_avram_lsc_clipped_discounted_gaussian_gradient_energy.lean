-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsc_clipped_discounted_gaussian_gradient_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T22:49:13.383533+00:00
-- url     : https://prove2.me/submissions/22adcd48-653d-45d4-a9bf-eae5206d90f2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen
import Theorems.Thm_AvramDividend_Classical_avram_lsc_compact_discounted_gaussian_gradient_energy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Clipping every reserve sample to an interior compact band gives a
genuinely bounded Gaussian Itô coefficient at each finite horizon. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hband : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q σ : ℝ) (hq : 0 ≤ q)
    (U : Ω → ℝ → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ T : ℝ, 0 < T →
        ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T,
          (‖(if 0 ≤ s then
              Real.exp (-(q * s)) *
                deriv w (max a (min b (U ω s))) * σ
            else 0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  have hopen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen C
  let V : Ω → ℝ → ℝ := fun ω s => max a (min b (U ω s))
  have hV : ∀ ω s, 0 ≤ s → V ω s ∈ Icc a b := by
    intro ω s _
    change a ≤ max a (min b (U ω s)) ∧
      max a (min b (U ω s)) ≤ b
    exact ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  exact avram_lsc_compact_discounted_gaussian_gradient_energy
    w C hw_smooth hopen a b hband q σ hq V hV


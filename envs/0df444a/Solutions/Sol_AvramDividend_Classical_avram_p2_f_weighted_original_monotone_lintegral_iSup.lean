-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_monotone_lintegral_iSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:49:36.516009+00:00
-- url     : https://prove2.me/submissions/c9f2ce0f-1b95-4131-92fe-bc6132e8e6ec

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Monotone convergence for increasingly approximated weights of the
true original Lévy intrinsic marked future count, with infinite values. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (H : ℕ → Ω → ℝ≥0∞) (hMeas : ∀ n, Measurable (H n))
    (hMono : Monotone H) :
    (∫⁻ ω, (⨆ n : ℕ, H n ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B)) ∂P) =
    ⨆ n : ℕ, (∫⁻ ω, H n ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) := by
  have hNmeas : Measurable (fun ω => ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B)) :=
    avram_p2_f_weighted_original_intrinsic_rectangle_measurable X s T B hB
  have hMeasProd : ∀ n : ℕ, Measurable (fun ω => H n ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B)) := by
    intro n
    exact (hMeas n).mul hNmeas
  have hMonoProd : Monotone (fun n : ℕ => fun ω => H n ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B)) := by
    intro i j hij ω
    exact mul_le_mul_of_nonneg_right (hMono hij ω) (zero_le)
  exact MeasureTheory.lintegral_iSup hMeasProd hMonoProd

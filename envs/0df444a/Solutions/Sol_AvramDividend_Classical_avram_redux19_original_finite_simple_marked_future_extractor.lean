-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux19_original_finite_simple_marked_future_extractor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:21:06.049285+00:00
-- url     : https://prove2.me/submissions/6aeb5eea-011b-4f3e-a55f-87fee0afc31e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-! Measurable finite simple weighted marked count on the same original future path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0) (hst : s ≤ t)
    (n : ℕ) (B : Fin n → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (w : Fin n → ℝ≥0∞) :
    ∃ Fpath : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable Fpath ∧
      ∀ ω : Ω,
      (∑ i : Fin n, w i *
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B i)) =
        Fpath (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) := by
  classical
  choose F hF hEq using (fun i : Fin n =>
    AvramDividend.Classical.avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
      X s t hst (B i) (hB i))
  refine ⟨fun Y => ∑ i : Fin n, w i * F i Y, ?_, ?_⟩
  · exact Finset.measurable_sum Finset.univ (fun i _ => measurable_const.mul (hF i))
  · intro ω
    change (∑ i : Fin n, w i *
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B i)) =
      ∑ i : Fin n, w i * F i (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)
    apply Finset.sum_congr rfl
    intro i _
    rw [hEq i ω]

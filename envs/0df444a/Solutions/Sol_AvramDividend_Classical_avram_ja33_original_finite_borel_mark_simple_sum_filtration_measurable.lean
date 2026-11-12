-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja33_original_finite_borel_mark_simple_sum_filtration_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:16:35.093147+00:00
-- url     : https://prove2.me/submissions/4167da8f-3189-48e8-8e3f-b2a9c7931ba0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja31_original_borel_mark_count_filtration_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every original finite Borel mark-simple compensated source sum is
measurable at the physical terminal filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0)
    (K : ℕ) (B : ℕ → Set ℝ) (c : ℕ → ℝ)
    (hB : ∀ i ∈ Finset.range K, MeasurableSet (B i)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    Measurable[𝓕 t] (fun ω : Ω =>
      ∑ i ∈ Finset.range K,
        c i * ((NX ω (Ioc 0 t ×ˢ B i)).toReal -
          (((t : ℝ≥0∞) * X.ν (B i)).toReal))) := by
  classical
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  change Measurable[𝓕 t] (fun ω : Ω =>
    ∑ i ∈ Finset.range K,
      c i * ((NX ω (Ioc 0 t ×ˢ B i)).toReal -
        (((t : ℝ≥0∞) * X.ν (B i)).toReal)))
  apply Finset.measurable_sum
  intro i hi
  have hCount : Measurable[𝓕 t]
      (fun ω : Ω => NX ω (Ioc 0 t ×ˢ B i)) := by
    exact avram_ja31_original_borel_mark_count_filtration_measurable
      X t (B i) (hB i hi)
  exact measurable_const.mul
    ((ENNReal.measurable_toReal.comp hCount).sub measurable_const)

-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_countable_simple_integral_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:56:26.737507+00:00
-- url     : https://prove2.me/submissions/58f5e698-c508-49b5-855f-8ae31f3b02b9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_countable_simple_pathwise
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_random_measure_countable_weighted_mass_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The genuine Lévy source marked-jump countable simple integral is measurable
as a sample-space function, using literal per-cell source-count measurability. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ι → ℝ≥0)
    (B : ι → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (H : ι → Ω → ℝ≥0∞)
    (hH : ∀ i, Measurable[𝓕 (s i)] (H i)) :
    Measurable (fun ω =>
      (∫⁻ p, ∑' i, (Ioc (s i) (s i + T i) ×ˢ B i).indicator (fun _ => H i ω) p ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))) := by
  let M : Ω → Measure (ℝ≥0 × ℝ) := fun ω => ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let C : ι → Set (ℝ≥0 × ℝ) := fun i => (Ioc (s i) (s i + T i) ×ˢ B i)
  have hCells (i : ι) : Measurable (fun ω => M ω (C i)) := by
    change Measurable (fun ω => ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc (s i) (s i + T i) ×ˢ B i))
    exact avram_p2_f_weighted_original_intrinsic_rectangle_measurable
      X (s i) (T i) (B i) (hB i)
  have hAmbient (i : ι) : Measurable (H i) :=
    (hH i).mono (𝓕.le (s i)) le_rfl
  have hSeries : Measurable (fun ω => ∑' i, H i ω * M ω (C i)) :=
    avram_p2_f_weighted_random_measure_countable_weighted_mass_measurable
      M C H hAmbient hCells
  have hPath (ω : Ω) :
      (∫⁻ p, ∑' i, (C i).indicator (fun _ => H i ω) p ∂M ω) =
      ∑' i, H i ω * M ω (C i) := by
    simpa only [M, C] using
      (avram_p2_f_weighted_original_intrinsic_countable_simple_pathwise
        X s (fun i => s i + T i) B hB H ω)
  have hFunc :
      (fun ω => (∫⁻ p, ∑' i, (C i).indicator (fun _ => H i ω) p ∂M ω)) =
      (fun ω => ∑' i, H i ω * M ω (C i)) := by
    funext ω
    exact hPath ω
  change Measurable
    (fun ω => (∫⁻ p, ∑' i, (C i).indicator (fun _ => H i ω) p ∂M ω))
  rw [hFunc]
  exact hSeries

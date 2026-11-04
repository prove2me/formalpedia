-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_original_uniform_grid_bochner_mean_rate_from_smalltime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:31:46.079449+00:00
-- url     : https://prove2.me/submissions/5b2d9f8f-9231-43ca-83b2-2a58af87fbd2

import Mathlib.Probability.IdentDistrib
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_uniform_real_grid_mean
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_smalltime_rescale_uniform_grid

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal BigOperators

/-- The actual original uniform-grid Bochner means inherit their one-cell small-time rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g)) (L : ℝ)
    (hRate : Tendsto
      (fun h : ℝ => (∫ ω, g (X.X (Real.toNNReal h) ω) ∂P) / h)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L)) :
    Tendsto (fun n : ℕ => ∫ ω,
      ∑ i ∈ Finset.range (n + 1),
        g (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
           X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω) ∂P)
      atTop (nhds ((T : ℝ) * L)) := by
  have hSmall := avram_p2_j_ui_smalltime_rescale_uniform_grid
    T hT (fun h : ℝ => ∫ ω, g (X.X (Real.toNNReal h) ω) ∂P) L hRate
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hc
  have hGrid (n : ℕ) :=
    avram_p2_j_ui_original_uniform_real_grid_mean
      X T n g hg.measurable (by
        have hXm : Measurable (X.X (T / ((n : ℝ≥0) + 1))) :=
          (X.adapted _).mono (𝓕.le _) le_rfl
        apply Integrable.of_bound ((hg.measurable.comp hXm).aestronglyMeasurable) C
        exact Filter.Eventually.of_forall (fun ω => hC (X.X _ ω)))
  have hcoe (n : ℕ) :
      Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1)) =
      T / ((n : ℝ≥0) + 1) := by
    have hden : ((n : ℝ) + 1) = (((n : ℝ≥0) + 1) : ℝ) := by norm_cast
    rw [hden, Real.toNNReal_div (NNReal.coe_nonneg T)]
    simp
  have hFunction :
      (fun n : ℕ => ∫ ω,
        ∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
             X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω) ∂P) =
      (fun n : ℕ => ((n : ℝ) + 1) *
        ∫ ω, g (X.X (Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω) ∂P) := by
    funext n
    rw [hcoe n]
    exact hGrid n
  rw [hFunction]
  exact hSmall

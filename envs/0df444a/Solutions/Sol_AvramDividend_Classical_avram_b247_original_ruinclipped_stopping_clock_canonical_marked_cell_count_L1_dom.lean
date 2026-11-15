-- Prove2me | solution 1 for AvramDividend.Classical.avram_b247_original_ruinclipped_stopping_clock_canonical_marked_cell_count_L1_dom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:31:49.010515+00:00
-- url     : https://prove2.me/submissions/f6d647fb-afef-4ea5-adc4-5b204b60c17a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_stopping_clock_measurable_from_filtration
import Theorems.Thm_AvramDividend_Classical_avram_b243_original_ruinclipped_finiteactivity_true_physical_marked_cell_count_L1_dom
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n m : ℕ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0)) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let grid : Ω → ℕ → ℝ≥0 := fun ω i =>
      min ((i : ℝ≥0) * Δ) (σ ω)
    let marked : Ω → Finset ℕ := fun ω => by
      classical
      exact (Finset.range (m + 1)).filter (fun i =>
        ∃ u : ℝ≥0, grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
          X.X u ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) u ≠ 0)
    Measurable (fun ω => ((marked ω).card : ℝ)) ∧
    Integrable (fun ω => ((marked ω).card : ℝ)) P ∧
    (∀ᵐ ω ∂P, ((marked ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) u)))
        (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ))).toReal) := by
  have hMeas : Measurable σ :=
    avram_p3_b_bvjump_original_stopping_clock_measurable_from_filtration
      σ hσstop
  exact avram_b243_original_ruinclipped_finiteactivity_true_physical_marked_cell_count_L1_dom
    X hFinite n m σ hMeas hσbound

-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_original_centered_nnreal_compact_existential_both
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:33:07.880605+00:00
-- url     : https://prove2.me/submissions/8a139498-7e4b-4043-93f1-db96705d5814

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_centered_nnreal_compact_mean_bridge

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-! Native almost-everywhere existence of a centered NNReal grid limit yields a single integrable real limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Set.Iio (0 : ℝ))
    (hex : ∀ᵐ ω ∂P, ∃ z : ℝ, Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
        g ((X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω - X.X 0 ω) -
           (X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω - X.X 0 ω)))
      atTop (nhds z)) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧
      Tendsto (fun n : ℕ => eLpNorm
        ((fun ω => ∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
             X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω)) - Z)
        1 P) atTop (nhds 0) ∧
      Tendsto (fun n : ℕ => ∫ ω,
        (∑ i ∈ Finset.range (n + 1),
          g (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
             X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω)) ∂P)
        atTop (nhds (∫ ω, Z ω ∂P)) := by
  classical
  let Y : ℕ → Ω → ℝ := fun n ω =>
    ∑ i ∈ Finset.range (n + 1),
      g ((X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω - X.X 0 ω) -
         (X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω - X.X 0 ω))
  let Z : Ω → ℝ := fun ω =>
    if h : ∃ z : ℝ, Tendsto (fun n => Y n ω) atTop (nhds z)
    then Classical.choose h else 0
  have hexY : ∀ᵐ ω ∂P, ∃ z : ℝ,
      Tendsto (fun n => Y n ω) atTop (nhds z) := by
    simpa only [Y] using hex
  have hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω)) := by
    filter_upwards [hexY] with ω hω
    simpa only [Z, dif_pos hω] using Classical.choose_spec hω
  have hBoth :=
    avram_p2_j_ui_original_centered_nnreal_compact_mean_bridge
      P X T hT g hg hc hneg Z (by simpa only [Y] using hae)
  exact ⟨Z, hBoth⟩

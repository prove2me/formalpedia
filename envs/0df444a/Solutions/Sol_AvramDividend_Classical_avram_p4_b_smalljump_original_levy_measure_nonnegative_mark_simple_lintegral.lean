-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_levy_measure_nonnegative_mark_simple_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:32:20.632924+00:00
-- url     : https://prove2.me/submissions/00cc2763-47d8-49e6-afbf-0ef848ff6e3f

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Integrating a finite nonnegative mark-simple kernel against the original
Lévy measure is the finite weighted sum of its original band masses. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (c : ι → ℝ≥0∞) :
    (∫⁻ z : ℝ, ∑ i ∈ S, (B i).indicator (fun _ => c i) z ∂X.ν) =
      ∑ i ∈ S, c i * X.ν (B i) := by
  have hm (i : ι) (hi : i ∈ S) :
      Measurable (fun z : ℝ => (B i).indicator (fun _ => c i) z) :=
    measurable_const.indicator (hB i hi)
  rw [lintegral_finset_sum S hm]
  apply Finset.sum_congr rfl
  intro i hi
  exact lintegral_indicator_const (hB i hi) (c i)

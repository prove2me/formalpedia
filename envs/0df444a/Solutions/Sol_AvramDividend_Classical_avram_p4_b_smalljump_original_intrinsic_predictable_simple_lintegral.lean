-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_predictable_simple_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:18:37.316238+00:00
-- url     : https://prove2.me/submissions/76501555-33fc-449e-99c2-1d92e0caaf06

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped ENNReal NNReal

/-- Genuine intrinsic original-jump count compensation extends from
predictable rectangles to nonnegative finite simple indicators. The
source-cell law hCell is exposed because P2's theorem is still Open. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (S : Finset ι)
    (s t : ι → ℝ≥0) (A : ι → Set Ω)
    (B : ι → Set ℝ) (J : ι → Ω → ℝ≥0∞)
    (hJsource : ∀ i ∈ S, ∀ ω,
      J i ω = ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i))
    (hJmeas : ∀ i ∈ S, Measurable (J i))
    (hA : ∀ i ∈ S, MeasurableSet[𝓕 (s i)] (A i))
    (hCell : ∀ i ∈ S,
      (∫⁻ ω in A i, J i ω ∂P) =
        P (A i) * ((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) :
    (∫⁻ ω, ∑ i ∈ S, (A i).indicator (J i) ω ∂P) =
      ∑ i ∈ S, P (A i) * ((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i) := by
  classical
  have hAm : ∀ i ∈ S, MeasurableSet (A i) := by
    intro i hi
    exact measurableSet_of_filtration (hA i hi)
  have hF : ∀ i ∈ S, Measurable ((A i).indicator (J i)) := by
    intro i hi
    exact (hJmeas i hi).indicator (hAm i hi)
  calc
    (∫⁻ ω, ∑ i ∈ S, (A i).indicator (J i) ω ∂P) =
        ∑ i ∈ S, ∫⁻ ω, (A i).indicator (J i) ω ∂P :=
          lintegral_finsetSum S hF
    _ = ∑ i ∈ S, ∫⁻ ω in A i, J i ω ∂P := by
      apply Finset.sum_congr rfl
      intro i hi
      exact lintegral_indicator (hAm i hi) (J i)
    _ = ∑ i ∈ S,
        P (A i) * ((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hCell i hi

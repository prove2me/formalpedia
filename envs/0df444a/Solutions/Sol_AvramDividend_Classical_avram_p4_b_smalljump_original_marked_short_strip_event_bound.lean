-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_marked_short_strip_event_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:28:59.320745+00:00
-- url     : https://prove2.me/submissions/e399936a-a2a5-49cc-a2c6-089f33e93772

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal

/-- The original intrinsic small-jump count in a short time strip,
restricted to any past event (including a right-continuous past event),
is bounded by its unconditional original-source Lévy intensity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s r : ℝ≥0) (B : Set ℝ) (A : Set Ω)
    (hRate :
      (∫⁻ ω,
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s r ×ˢ B) ∂P) =
          ((r - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    (∫⁻ ω in A,
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s r ×ˢ B) ∂P) ≤
          ((r - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
  let J : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s r ×ˢ B)
  change (∫⁻ ω in A, J ω ∂P) ≤
    ((r - s : ℝ≥0) : ℝ≥0∞) * X.ν B
  calc
    (∫⁻ ω in A, J ω ∂P) ≤ ∫⁻ ω, J ω ∂P := by
      simpa using
        (lintegral_mono_set (Set.subset_univ A) :
          (∫⁻ ω in A, J ω ∂P) ≤
            (∫⁻ ω in Set.univ, J ω ∂P))
    _ = ((r - s : ℝ≥0) : ℝ≥0∞) * X.ν B := hRate

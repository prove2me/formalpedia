-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_time_mark_grid_integral_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:06:25.159914+00:00
-- url     : https://prove2.me/submissions/57ee1692-cbdf-43c2-8a3a-8bed74c2bc0d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Genuine source P2 finite-band rates identify the expectation of the
original intrinsic jump integral of an arbitrary finite time-mark grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι) (s t : ι → ℝ≥0)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (c : ι → ℝ≥0∞) (J : ι → Ω → ℝ≥0∞)
    (hJsource : ∀ i ω, J i ω =
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i))
    (hMeas : ∀ i ∈ S, Measurable (J i))
    (hRate : ∀ i ∈ S, (∫⁻ ω, J i ω ∂P) =
      (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))) :
    (∫⁻ ω, (∫⁻ p : ℝ≥0 × ℝ,
      ∑ i ∈ S, (Ioc (s i) (t i) ×ˢ B i).indicator
        (fun _ => c i) p
      ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ∂P) =
    ∑ i ∈ S, c i * (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) := by
  let N : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  have hPath (ω : Ω) :
      (∫⁻ p, ∑ i ∈ S,
        (Ioc (s i) (t i) ×ˢ B i).indicator (fun _ => c i) p ∂N ω) =
      ∑ i ∈ S, c i * N ω (Ioc (s i) (t i) ×ˢ B i) := by
    have hm (i : ι) (hi : i ∈ S) : Measurable
        (fun p : ℝ≥0 × ℝ =>
          (Ioc (s i) (t i) ×ˢ B i).indicator (fun _ => c i) p) :=
      measurable_const.indicator (measurableSet_Ioc.prod (hB i hi))
    rw [lintegral_finset_sum S hm]
    apply Finset.sum_congr rfl
    intro i hi
    exact lintegral_indicator_const
      (measurableSet_Ioc.prod (hB i hi)) (c i)
  change (∫⁻ ω, (∫⁻ p, ∑ i ∈ S,
    (Ioc (s i) (t i) ×ˢ B i).indicator (fun _ => c i) p ∂N ω) ∂P) = _
  calc
    _ = (∫⁻ ω, ∑ i ∈ S, c i * J i ω ∂P) := by
      apply lintegral_congr_ae
      filter_upwards [] with ω
      rw [hPath ω]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hJsource i ω]
    _ = ∑ i ∈ S, (∫⁻ ω, c i * J i ω ∂P) := by
      rw [lintegral_finset_sum S]
      intro i hi
      exact measurable_const.mul (hMeas i hi)
    _ = ∑ i ∈ S, c i * (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [lintegral_const_mul (c i) (hMeas i hi), hRate i hi]

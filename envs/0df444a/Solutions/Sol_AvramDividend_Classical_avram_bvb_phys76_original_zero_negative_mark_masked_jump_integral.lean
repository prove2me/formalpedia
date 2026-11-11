-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys76_original_zero_negative_mark_masked_jump_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T01:22:42.312914+00:00
-- url     : https://prove2.me/submissions/47dffe21-b9fe-42cf-b010-4113b9800c82

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original stopped jump integral vanishes if its exact time-mark
support is a null negative-intrinsic-mark rectangle. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (hZero : ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hSupport : ∀ p : ℝ≥0 × ℝ, H ((p.1, ω), p.2) ≠ 0 →
      p ∈ Ioc (0 : ℝ≥0) T ×ˢ Iio (0 : ℝ)) :
    (∫ p, H ((p.1, ω), p.2)
      ∂((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u)))) = 0 := by
  let μ : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u)))
  have hAE : ∀ᵐ p ∂μ, p ∉ Ioc (0 : ℝ≥0) T ×ˢ Iio (0 : ℝ) := by
    apply (ae_iff).2
    have hμZero : μ (Ioc (0 : ℝ≥0) T ×ˢ Iio (0 : ℝ)) = 0 := hZero
    have hset :
        {p : ℝ≥0 × ℝ | ¬ p ∉ Ioc (0 : ℝ≥0) T ×ˢ Iio (0 : ℝ)} =
          Ioc (0 : ℝ≥0) T ×ˢ Iio (0 : ℝ) := by
      apply Set.ext
      intro p
      exact not_not
    rw [hset]
    exact hμZero
  change (∫ p, H ((p.1, ω), p.2) ∂μ) = 0
  apply integral_eq_zero_of_ae
  filter_upwards [hAE] with p hp
  by_contra hn
  exact hp (hSupport p hn)

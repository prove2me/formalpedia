-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf13_original_adjacent_annulus_centred_cross_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T18:23:45.436424+00:00
-- url     : https://prove2.me/submissions/118dc0f8-11ac-4f47-8f9e-fd643ea2d370

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_original_adjacent_annulus_compensated_covariance_zero
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

/-- Reuse the original-path adjacent-annulus covariance proof verbatim. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m p : ℕ) (hnm : n ≤ m) (hmp : m ≤ p) :
    let B : ℕ → ℕ → Set ℝ := fun a b =>
      Ioc (-(1 / ((a : ℝ) + 1))) (-(1 / ((b : ℝ) + 1)))
    let N : ℕ → ℕ → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B a b)
    let r : ℕ → ℕ → ℝ := fun a b =>
      ((T : ℝ≥0∞) * X.ν (B a b)).toReal
    Integrable (fun ω =>
      ((N n m ω).toReal - r n m) *
      ((N m p ω).toReal - r m p)) P ∧
    (∫ ω, ((N n m ω).toReal - r n m) *
      ((N m p ω).toReal - r m p) ∂P) = 0 := by
  exact avram_mix_inf15_original_adjacent_annulus_compensated_covariance_zero
    X T n m p hnm hmp

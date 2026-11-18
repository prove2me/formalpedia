-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_physical_zero_count_laplace_cell_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:11:05.443268+00:00
-- url     : https://prove2.me/submissions/0dce5c93-f089-4783-bafd-c162a25639fa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_negative_zero_count_exponential_one_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_zero_poisson_count_cell_integral_20261117
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The actual physical negative-jump Laplace integral on a zero-count event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (J : Ω → ℝ)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
      else 0)
    (K : Ω → ℕ) (r : ℝ≥0)
    (hK : Measurable K) (hLaw : HasLaw K (poissonMeasure r) P)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal) :
    (∫ ω in {ω : Ω | K ω = 0}, Real.exp (θ * J ω) ∂P) =
      (poissonMeasure r).real {0} := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have h0 := avram_a27_original_negative_zero_count_exponential_one_20261117
    X hFinite t θ J hJEq K hK hCount
  exact avram_a27_zero_poisson_count_cell_integral_20261117
    P K hK r hLaw (fun ω => Real.exp (θ * J ω)) h0

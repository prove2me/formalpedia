-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_20261115_original_Borel_count_real_charfun_poisson
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:19:31.466073+00:00
-- url     : https://prove2.me/submissions/08e52435-a476-4afc-a962-3b37da629310
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a25_original_negative_Borel_count_all_factorial_moments_20261115
import Theorems.Thm_AvramDividend_Classical_avram_a25_poisson_characteristic_from_all_factorial_moments_20261115
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)).toReal)
    (r : ℝ≥0)
    (hr : (r : ℝ) = ((T : ℝ≥0∞) * X.ν B).toReal)
    (hRatePos : 0 < r) :
    ∀ u : ℝ,
      charFun (P.map (fun ω => (K ω : ℝ))) u =
        charFun ((poissonMeasure r).map (fun n : ℕ => (n : ℝ))) u := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hMom : ∀ n : ℕ,
      (∫ ω, (Nat.descFactorial (K ω) n : ℝ) ∂P) = (r : ℝ) ^ n :=
    avram_a25_original_negative_Borel_count_all_factorial_moments_20261115
      X hFinite T B hB hNeg K hK hCount r hr
  exact avram_a25_poisson_characteristic_from_all_factorial_moments_20261115
    P K hK r hMom

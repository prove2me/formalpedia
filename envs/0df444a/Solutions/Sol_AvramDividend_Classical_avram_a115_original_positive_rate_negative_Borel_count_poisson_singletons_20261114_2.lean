-- Prove2me | solution 2 for AvramDividend.Classical.avram_a115_original_positive_rate_negative_Borel_count_poisson_singletons_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:45:49.512902+00:00
-- url     : https://prove2.me/submissions/2795a019-7c14-41d4-87c8-5fc385c5c445

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a25_original_negative_Borel_count_all_factorial_moments_20261115
import Theorems.Thm_AvramDividend_Classical_avram_a25_poisson_characteristic_from_all_factorial_moments_positive_rate_20261115
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact singleton Poisson probabilities from physical factorial moments. -/
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
    ∀ k : ℕ, P {ω : Ω | K ω = k} = poissonMeasure r {k} := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hMom :=
    avram_a25_original_negative_Borel_count_all_factorial_moments_20261115
      X hFinite T B hB hNeg K hK hCount r hr
  have hCF :=
    avram_a25_poisson_characteristic_from_all_factorial_moments_positive_rate_20261115
      P K hK r hRatePos hMom
  have hNat : Measurable (fun n : ℕ => (n : ℝ)) := measurable_of_countable _
  have hReal : Measurable (fun ω : Ω => (K ω : ℝ)) :=
    hNat.comp hK
  letI : IsProbabilityMeasure (P.map (fun ω => (K ω : ℝ))) :=
    Measure.isProbabilityMeasure_map hReal.aemeasurable
  letI : IsProbabilityMeasure ((poissonMeasure r).map (fun n : ℕ => (n : ℝ))) :=
    Measure.isProbabilityMeasure_map hNat.aemeasurable
  have hMap : P.map (fun ω => (K ω : ℝ)) =
      (poissonMeasure r).map (fun n : ℕ => (n : ℝ)) := by
    apply Measure.ext_of_charFun
    funext u
    exact hCF u
  intro k
  calc
    P {ω : Ω | K ω = k} =
        (P.map (fun ω => (K ω : ℝ))) {(k : ℝ)} := by
      rw [Measure.map_apply hReal (measurableSet_singleton (k : ℝ))]
      simp [Set.preimage]
    _ = ((poissonMeasure r).map (fun n : ℕ => (n : ℝ))) {(k : ℝ)} := by
      rw [hMap]
    _ = poissonMeasure r {k} := by
      rw [Measure.map_apply hNat (measurableSet_singleton (k : ℝ))]
      simp [Set.preimage]

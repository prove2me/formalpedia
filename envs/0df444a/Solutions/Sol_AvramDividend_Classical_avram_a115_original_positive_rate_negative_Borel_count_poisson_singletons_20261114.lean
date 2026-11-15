-- Prove2me | solution 1 for AvramDividend.Classical.avram_a115_original_positive_rate_negative_Borel_count_poisson_singletons_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:10:49.657617+00:00
-- url     : https://prove2.me/submissions/99c545c8-924e-45cf-80b6-c552b6fab9a9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_FamousTheorems_char_fun_determines_measure_6b
import Theorems.Thm_AvramDividend_Classical_avram_a25_20261115_original_Borel_count_real_charfun_poisson
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
    ∀ k : ℕ, P {ω : Ω | K ω = k} = poissonMeasure r {k} := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hcast : Measurable (fun n : ℕ => (n : ℝ)) :=
    measurable_of_countable _
  have hm : Measurable (fun ω : Ω => (K ω : ℝ)) :=
    hcast.comp hK
  have hc : charFun (P.map (fun ω : Ω => (K ω : ℝ))) =
      charFun ((poissonMeasure r).map (fun n : ℕ => (n : ℝ))) := by
    funext u
    exact avram_a25_20261115_original_Borel_count_real_charfun_poisson
      X hFinite T B hB hNeg K hK hCount r hr hRatePos u
  have hmaps : P.map (fun ω : Ω => (K ω : ℝ)) =
      (poissonMeasure r).map (fun n : ℕ => (n : ℝ)) :=
    FamousTheorems.char_fun_determines_measure_6b hc
  intro k
  have hp : (fun ω : Ω => (K ω : ℝ)) ⁻¹' {((k : ℕ) : ℝ)} =
      {ω : Ω | K ω = k} := by
    ext ω
    simp
  have hq : (fun n : ℕ => (n : ℝ)) ⁻¹' {((k : ℕ) : ℝ)} =
      ({k} : Set ℕ) := by
    ext n
    simp
  calc
    P {ω : Ω | K ω = k} =
        (P.map (fun ω : Ω => (K ω : ℝ))) {((k : ℕ) : ℝ)} := by
          rw [Measure.map_apply hm (measurableSet_singleton ((k : ℕ) : ℝ)), hp]
    _ = ((poissonMeasure r).map (fun n : ℕ => (n : ℝ))) {((k : ℕ) : ℝ)} := by
          rw [hmaps]
    _ = poissonMeasure r {k} := by
          rw [Measure.map_apply hcast (measurableSet_singleton ((k : ℕ) : ℝ)), hq]

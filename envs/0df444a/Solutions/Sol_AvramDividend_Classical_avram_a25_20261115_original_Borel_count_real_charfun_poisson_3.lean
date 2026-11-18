-- Prove2me | solution 3 for AvramDividend.Classical.avram_a25_20261115_original_Borel_count_real_charfun_poisson
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:35:31.7369+00:00
-- url     : https://prove2.me/submissions/73dd965f-3ec2-4719-8ca7-673c29aa5320

import Mathlib.Probability.HasLaw
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Measure.Map
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_source_original_negative_Borel_count_HasLaw_of_true_count_20261118
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
  have hLaw :=
    avram_a27_source_original_negative_Borel_count_HasLaw_of_true_count_20261118
      X hFinite T B hB hNeg K hK hCount r hr
  have hCastMeas : Measurable (fun n : ℕ => (n : ℝ)) :=
    measurable_of_countable _
  have hMap :
      P.map (fun ω => (K ω : ℝ)) =
        (poissonMeasure r).map (fun n : ℕ => (n : ℝ)) := by
    calc
      P.map (fun ω => (K ω : ℝ)) =
          (P.map K).map (fun n : ℕ => (n : ℝ)) := by
            simpa only [Function.comp_def] using
              (Measure.map_map hCastMeas hK).symm
      _ = (poissonMeasure r).map (fun n : ℕ => (n : ℝ)) := by
        rw [hLaw.map_eq]
  intro u
  rw [hMap]

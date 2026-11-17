-- Prove2me | solution 3 for AvramDividend.Classical.avram_a115_original_positive_rate_negative_Borel_count_poisson_singletons_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T07:38:15.9532+00:00
-- url     : https://prove2.me/submissions/5566c4df-ef62-47e1-a720-c54dfdf8ce4d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a25_original_negative_Borel_binomial_grid_singleton_approx_20261115
import Theorems.Thm_AvramDividend_Classical_avram_a25_binomial_cell_limit_identifies_poisson_singletons_20261115
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
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
  obtain ⟨p, hp, hApprox⟩ :=
    avram_a25_original_negative_Borel_binomial_grid_singleton_approx_20261115
      X hFinite T B hB hNeg K hK hCount r hr
  have hLaw := avram_a25_binomial_cell_limit_identifies_poisson_singletons_20261115
    (P.map K) r p hp hApprox
  intro k
  calc
    P {ω : Ω | K ω = k} = P.map K {k} := by
      rw [Measure.map_apply hK (measurableSet_singleton k)]
      simp [Set.preimage]
    _ = poissonMeasure r {k} := hLaw k

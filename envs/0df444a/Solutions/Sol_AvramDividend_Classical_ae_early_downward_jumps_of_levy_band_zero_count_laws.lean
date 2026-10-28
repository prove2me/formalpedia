-- Prove2me | solution 1 for AvramDividend.Classical.ae_early_downward_jumps_of_levy_band_zero_count_laws
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:12:09.172974+00:00
-- url     : https://prove2.me/submissions/23a76bbd-4b4c-4769-8e3a-7c679a0e66fa

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_negative_jump_real_poisson_rates_tendsto_top
import Theorems.Thm_AvramDividend_Classical_zero_probability_of_poisson_count_no_jump_event
import Theorems.Thm_AvramDividend_Classical_ae_early_downward_jumps_of_null_no_jump_grid

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤)
    (δ : ℕ → ℝ≥0) (hδpos : ∀ k, 0 < δ k)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε → ∃ k, δ k < ε)
    (counts : ℕ → ℕ → Ω → ℕ)
    (hsubset : ∀ k n : ℕ,
      {ω : Ω | ¬ ∃ t : ℝ≥0, 0 < t ∧ t < δ k ∧
        ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
          (nhdsWithin t (Iio t)) (nhds l) ∧ X.X t ω < l}
        ⊆ {ω | counts k n ω = 0})
    (hzeroLaw : ∀ k n : ℕ,
      P {ω | counts k n ω = 0} =
        ENNReal.ofReal (Real.exp
          (-((δ k : ℝ) *
            (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)))) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧
        ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
          (nhdsWithin t (Iio t)) (nhds l) ∧ X.X t ω < l := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hnull (k : ℕ) :
      P {ω : Ω | ¬ ∃ t : ℝ≥0, 0 < t ∧ t < δ k ∧
        ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
          (nhdsWithin t (Iio t)) (nhds l) ∧ X.X t ω < l} = 0 := by
    apply zero_probability_of_poisson_count_no_jump_event
      P _ (counts k)
      (fun n : ℕ => (δ k : ℝ) *
        (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)
    · exact negative_jump_real_poisson_rates_tendsto_top
        X.ν X.ν_integrable hνinf (δ k : ℝ)
        (by exact_mod_cast hδpos k)
    · exact hsubset k
    · exact hzeroLaw k
  exact ae_early_downward_jumps_of_null_no_jump_grid
    X δ hcofinal hnull

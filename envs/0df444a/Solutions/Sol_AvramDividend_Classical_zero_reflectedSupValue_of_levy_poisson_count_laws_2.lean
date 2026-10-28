-- Prove2me | solution 2 for AvramDividend.Classical.zero_reflectedSupValue_of_levy_poisson_count_laws
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:55:38.103524+00:00
-- url     : https://prove2.me/submissions/fc27d303-e791-4adc-b5e2-e76d683d3ebb

import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_poisson_band_laws_and_deriv_top
import Theorems.Thm_AvramDividend_Classical_negative_jump_real_poisson_rates_tendsto_top

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (δ : ℕ → ℝ≥0) (counts : ℕ → ℕ → Ω → ℕ)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤)
    (hδpos : ∀ k : ℕ, 0 < δ k)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε → ∃ k : ℕ, δ k < ε)
    (hsubset : ∀ k n : ℕ,
      {ω : Ω | ¬ ∃ t : ℝ≥0, 0 < t ∧ t < δ k ∧
        ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
          (nhdsWithin t (Iio t)) (nhds l) ∧ X.X t ω < l}
        ⊆ {ω | counts k n ω = 0})
    (hzeroLaw : ∀ k n : ℕ,
      P {ω | counts k n ω = 0} =
        ENNReal.ofReal (Real.exp
          (-((δ k : ℝ) *
            (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal))))
    (hder : derivZeroPlus W = ⊤) :
    barrierSupValue X 0 q = ENNReal.ofReal (barrierValue W 0 0) := by
  apply zero_reflectedSupValue_of_poisson_band_laws_and_deriv_top
    X q W δ counts
    (fun k n => (δ k : ℝ) * (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)
    hcofinal
  · intro k
    apply negative_jump_real_poisson_rates_tendsto_top
      X.ν X.ν_integrable hνinf (δ k : ℝ)
    exact_mod_cast hδpos k
  · exact hsubset
  · exact hzeroLaw
  · exact hder

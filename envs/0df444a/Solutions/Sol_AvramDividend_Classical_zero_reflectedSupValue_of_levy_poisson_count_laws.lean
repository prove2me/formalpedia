-- Prove2me | solution 1 for AvramDividend.Classical.zero_reflectedSupValue_of_levy_poisson_count_laws
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:53:52.585746+00:00
-- url     : https://prove2.me/submissions/b1fd9708-1734-4bd0-b6f4-56681ecbc4e6

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_poisson_band_laws_and_deriv_top
import Theorems.Thm_AvramDividend_Classical_negative_jump_real_poisson_rates_tendsto_top
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- Canonical truncated negative-jump rates supply the Poisson-band divergence input. -/
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
  have hdiv (k : ℕ) :
      Tendsto
        (fun n : ℕ => (δ k : ℝ) *
          (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)
        atTop atTop := by
    exact negative_jump_real_poisson_rates_tendsto_top
      X.ν X.ν_integrable hνinf (δ k : ℝ) (by exact_mod_cast hδpos k)
  exact zero_reflectedSupValue_of_poisson_band_laws_and_deriv_top
    X q W δ counts
    (fun k n => (δ k : ℝ) *
      (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)
    hcofinal hdiv hsubset hzeroLaw hder

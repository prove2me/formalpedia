-- Prove2me | solution 1 for AvramDividend.Classical.zero_reflectedSupValue_of_poisson_band_laws_and_deriv_top
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:13:22.081997+00:00
-- url     : https://prove2.me/submissions/d3c0e3f6-7d8d-43f7-87cc-a1d32764699b

import Theorems.Thm_AvramDividend_Classical_zero_probability_of_poisson_count_no_jump_event
import Theorems.Thm_AvramDividend_Classical_ae_early_downward_jumps_of_null_no_jump_grid
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_ae_early_downward_jumps_and_deriv_top

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Poisson laws for shrinking initial intervals and infinite scale slope imply the zero-barrier identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (δ : ℕ → ℝ≥0) (counts : ℕ → ℕ → Ω → ℕ)
    (rates : ℕ → ℕ → ℝ)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε → ∃ k : ℕ, δ k < ε)
    (hdiv : ∀ k : ℕ, Tendsto (rates k) atTop atTop)
    (hsubset : ∀ k n : ℕ,
      {ω : Ω | ¬ ∃ t : ℝ≥0, 0 < t ∧ t < δ k ∧
        ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
          (nhdsWithin t (Iio t)) (nhds l) ∧ X.X t ω < l}
        ⊆ {ω | counts k n ω = 0})
    (hzeroLaw : ∀ k n : ℕ,
      P {ω | counts k n ω = 0} =
        ENNReal.ofReal (Real.exp (-(rates k n))))
    (hder : derivZeroPlus W = ⊤) :
    barrierSupValue X 0 q = ENNReal.ofReal (barrierValue W 0 0) := by 
  haveI := X.isProbability
  refine zero_reflectedSupValue_of_ae_early_downward_jumps_and_deriv_top X q W ?_ hder
  exact ae_early_downward_jumps_of_null_no_jump_grid X δ hcofinal fun k =>
    zero_probability_of_poisson_count_no_jump_event P _ (counts k) (rates k) (hdiv k)
      (hsubset k) (hzeroLaw k)

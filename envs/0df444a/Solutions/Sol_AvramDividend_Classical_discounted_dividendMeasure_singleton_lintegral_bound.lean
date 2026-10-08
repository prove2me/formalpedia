-- Prove2me | solution 1 for AvramDividend.Classical.discounted_dividendMeasure_singleton_lintegral_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:17:18.903977+00:00
-- url     : https://prove2.me/submissions/9b3c3128-de32-468b-916b-0d2140118495

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_discounted_dividendMeasure_atom_exponential_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissible X x D) (θ q : ℝ) (hθ : 1 ≤ θ)
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in {(t : ℝ)}, ENNReal.ofReal (Real.exp (-(q * s)))
       ∂(dividendMeasure D ω)) ≤
    ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) *
      (Real.exp (θ * riskProcess X x D t ω) -
        Real.exp (θ * (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω))))) := by
  rw [lintegral_singleton]
  exact discounted_dividendMeasure_atom_exponential_bound
    X x D hD θ q hθ ω t ht

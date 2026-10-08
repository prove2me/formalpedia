-- Prove2me | solution 1 for AvramDividend.Classical.discounted_dividendMeasure_finset_lintegral_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:17:23.070921+00:00
-- url     : https://prove2.me/submissions/b8764721-2d3e-4083-898c-2ec02755b787

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
    (ω : Ω) (S : Finset ℝ)
    (hNonneg : ∀ s ∈ S, 0 ≤ s)
    (hActive : ∀ s ∈ S,
      s.toNNReal = 0 ∨ (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in (S : Set ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
    ∑ s ∈ S, ENNReal.ofReal (Real.exp (-(q * s)) *
      (Real.exp (θ * riskProcess X x D s.toNNReal ω) -
        Real.exp (θ * (riskProcess X x D s.toNNReal ω -
          (rightLimit D s.toNNReal ω - D s.toNNReal ω))))) := by
  rw [lintegral_finset]
  refine Finset.sum_le_sum ?_
  intro s hs
  have hEq : (s.toNNReal : ℝ) = s :=
    Real.coe_toNNReal s (hNonneg s hs)
  have hBound := discounted_dividendMeasure_atom_exponential_bound
    X x D hD θ q hθ ω s.toNNReal (hActive s hs)
  simpa only [hEq] using hBound

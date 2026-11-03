-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat07b_original_discounted_HJB_rightpayment_atom_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T11:02:40.441875+00:00
-- url     : https://prove2.me/submissions/20dbffb9-ed97-4619-bc96-3f807ec3340f

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The actual discounted right-payment singleton is controlled by its HJB value drop,
including simultaneous source jumps and the time-zero payment atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ (ω : Ω) (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    ENNReal.ofReal (Real.exp (-(q * (t : ℝ)))) *
      dividendMeasure D ω {(t : ℝ)} ≤
    ENNReal.ofReal (Real.exp (-(q * (t : ℝ)))) *
      ENNReal.ofReal
        (w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) := by
  rw [dividendMeasure_singleton_eq_rightLimit_sub D hD ω t]
  exact mul_le_mul_of_nonneg_left
    (ENNReal.ofReal_le_ofReal (hjump ω t ht))
    (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (-(q * (t : ℝ)))) from zero_le)

-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat07b_original_discounted_HJB_all_rightpayment_atom_tsum_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T11:22:03.340976+00:00
-- url     : https://prove2.me/submissions/de7f2895-f0b0-4450-8a26-5e11d60878d8

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_chat07b_original_discounted_HJB_rightpayment_atom_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

/-- The canonical pre-ruin HJB right-payment inequality dominates the full
ENNReal sum of actual discounted singleton masses on any chosen active set. -/
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
    (ω : Ω) (S : Set ℝ≥0)
    (hActive : ∀ t ∈ S, t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    (∑' t : S,
      ENNReal.ofReal (Real.exp (-(q * (t.1 : ℝ)))) *
        dividendMeasure D ω {(t.1 : ℝ)}) ≤
    (∑' t : S,
      ENNReal.ofReal (Real.exp (-(q * (t.1 : ℝ)))) *
        ENNReal.ofReal
          (w (riskProcess X x D t.1 ω) -
            w (riskProcess X x D t.1 ω -
              (rightLimit D t.1 ω - D t.1 ω)))) := by
  exact ENNReal.tsum_le_tsum (fun t =>
    avram_chat07b_original_discounted_HJB_rightpayment_atom_bound
      X x D hD w q hjump ω t.1 (hActive t.1 t.2))

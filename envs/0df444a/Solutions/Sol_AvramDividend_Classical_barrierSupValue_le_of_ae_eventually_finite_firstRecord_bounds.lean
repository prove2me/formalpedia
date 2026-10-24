-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_le_of_ae_eventually_finite_firstRecord_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:36:18.442605+00:00
-- url     : https://prove2.me/submissions/3dff8b60-51b0-42ab-a4ad-f43c30aec993

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_sum_expected_firstRecord_budgets
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators Classical

/-! An almost surely finite record-cell cover bounds the complete stopped dividend reward in expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (a q : ℝ)
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n : ℕ, AEMeasurable (w n) P)
    (hfinite : ∀ᵐ ω ∂P, ∃ N : ℕ,
      (∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤
      (∑ n ∈ Finset.range N, w n ω)) :
    barrierSupValue X a q ≤ (∑' n, ∫⁻ ω, w n ω ∂P) := by
  apply barrierSupValue_le_sum_expected_firstRecord_budgets X a q w hw
  filter_upwards [hfinite] with ω hω
  obtain ⟨N, hN⟩ := hω
  rw [ENNReal.tsum_eq_iSup_nat]
  exact hN.trans (le_iSup (fun M : ℕ => ∑ n ∈ Finset.range M, w n ω) N)

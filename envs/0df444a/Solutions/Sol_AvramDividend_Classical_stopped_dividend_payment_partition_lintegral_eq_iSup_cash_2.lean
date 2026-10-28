-- Prove2me | solution 2 for AvramDividend.Classical.stopped_dividend_payment_partition_lintegral_eq_iSup_cash
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T19:53:40.176864+00:00
-- url     : https://prove2.me/submissions/e64e6523-e1b5-400e-9b35-644991167d39

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (D : ℝ≥0 → Ω → ℝ) (σ : ℝ≥0∞) (T q : ℝ) (ω : Ω)
    (S : ℕ → Set ℝ)
    (hMeas : ∀ k, MeasurableSet (S k))
    (hDisjoint : Pairwise (Function.onFun Disjoint S))
    (hCover : (⋃ k : ℕ, S k) = AvramDividend.Classical.paymentTimes σ ∩ Iic T) :
    (∫⁻ t in AvramDividend.Classical.paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(AvramDividend.Classical.dividendMeasure D ω)) =
      ⨆ n : ℕ, ∑ k ∈ Finset.range n,
        ∫⁻ t in S k,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(AvramDividend.Classical.dividendMeasure D ω) := by
  rw [← hCover, lintegral_iUnion hMeas hDisjoint, ENNReal.tsum_eq_iSup_nat]

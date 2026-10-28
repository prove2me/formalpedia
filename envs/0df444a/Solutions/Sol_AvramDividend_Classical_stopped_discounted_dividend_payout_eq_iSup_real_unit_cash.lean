-- Prove2me | solution 1 for AvramDividend.Classical.stopped_discounted_dividend_payout_eq_iSup_real_unit_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T20:15:22.780995+00:00
-- url     : https://prove2.me/submissions/04680aca-6bd4-4b4d-98f4-49bdf27137b9

import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_stopped_dividend_payment_partition_lintegral_eq_iSup_cash
import Theorems.Thm_AvramDividend_Classical_payment_window_nat_unit_intervals_partition
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Real-valued nonnegative interval cash gives the exact pathwise
    stopped Stieltjes payout in the form used by the Lévy-grid verification
    limit. Every half-open block retains continuous and atomic payments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (D : ℝ≥0 → Ω → ℝ) (σ : ℝ≥0∞) (T q : ℝ) (ω : Ω)
    (cash : ℕ → ℝ)
    (hCashNN : ∀ k : ℕ, 0 ≤ cash k)
    (hCashEq : ∀ k : ℕ,
      ENNReal.ofReal (cash k) =
        ∫⁻ t in (paymentTimes σ ∩ Iic T) ∩
          Ico (k : ℝ) ((k : ℝ) + 1),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) :
    (∫⁻ t in paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      ⨆ n : ℕ, ENNReal.ofReal
        (∑ k ∈ Finset.range n, cash k) := by
  have hPart :=
    AvramDividend.Classical.payment_window_nat_unit_intervals_partition σ T
  have hPayout :=
    AvramDividend.Classical.stopped_dividend_payment_partition_lintegral_eq_iSup_cash
      D σ T q ω
      (fun k : ℕ => (paymentTimes σ ∩ Iic T) ∩
        Ico (k : ℝ) ((k : ℝ) + 1))
      hPart.1 hPart.2.1 hPart.2.2
  have hSum : ∀ n : ℕ,
      ENNReal.ofReal (∑ k ∈ Finset.range n, cash k) =
        ∑ k ∈ Finset.range n, ENNReal.ofReal (cash k) := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        have hp : 0 ≤ ∑ k ∈ Finset.range n, cash k :=
          Finset.sum_nonneg (by intro k hk; exact hCashNN k)
        simp only [Finset.sum_range_succ]
        rw [ENNReal.ofReal_add hp (hCashNN n), ih]
  rw [hPayout]
  apply iSup_congr
  intro n
  calc
    (∑ k ∈ Finset.range n,
      ∫⁻ t in (paymentTimes σ ∩ Iic T) ∩
        Ico (k : ℝ) ((k : ℝ) + 1),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
        ∑ k ∈ Finset.range n, ENNReal.ofReal (cash k) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact (hCashEq k).symm
    _ = ENNReal.ofReal (∑ k ∈ Finset.range n, cash k) :=
      (hSum n).symm

-- Prove2me | solution 2 for AvramDividend.Classical.runningSup_finite_record_cells_with_terminal_discount_upper
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:24:21.086345+00:00
-- url     : https://prove2.me/submissions/8d058fee-8913-4f12-94dc-06fb940dad70

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_N_record_cells_discount_upper_bound
import Theorems.Thm_AvramDividend_Classical_runningSup_terminal_extended_clock_discount_upper
import Theorems.Thm_AvramDividend_Classical_stopped_lintegral_Ioc_adjacent_add

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q b h : ℝ) (hq : 0 ≤ q) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (N : ℕ) (u : ℕ → ℝ≥0) (t : ℝ≥0)
    (hu : ∀ k : ℕ, k ≤ N →
      (u k : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞)))
    (hord : ∀ k : ℕ, k < N → (u k : ℝ) ≤ (u (k + 1) : ℝ))
    (hstart : (u 0 : ℝ) ≤ (u N : ℝ))
    (hSurvive : ENNReal.ofReal (u N : ℝ) < τ)
    (hNt : (u N : ℝ) ≤ (t : ℝ))
    (ht : (t : ℝ≥0∞) ≤
      (⨅ (r : ℝ≥0)
        (_ : b + ((N + 1 : ℕ) : ℝ) * h < X.X r ω),
        (r : ℝ≥0∞))) :
    (∫⁻ r in paymentTimes τ,
       if r ∈ Set.Ioc (u 0 : ℝ) (t : ℝ)
       then ENNReal.ofReal (Real.exp (-(q * r))) else 0
       ∂(dividendMeasure (runningSup X) ω)) ≤
    ∑ k ∈ Finset.range (N + 1),
      ENNReal.ofReal (Real.exp (-(q * (u k : ℝ)))) * ENNReal.ofReal h := by
  rw [AvramDividend.Classical.stopped_lintegral_Ioc_adjacent_add _ _ _ _ _ _ hstart hNt, Finset.sum_range_succ]
  refine add_le_add (AvramDividend.Classical.runningSup_N_record_cells_discount_upper_bound X ω τ q hq b h hb hh
    N u hu hord hSurvive) ?_
  have e : b + ((N + 1 : ℕ) : ℝ) * h = (b + (N : ℝ) * h) + h := by push_cast; ring
  rw [e] at ht
  have hbN : 0 ≤ b + (N : ℝ) * h := by positivity
  exact (setLIntegral_le_lintegral _ _).trans
    (AvramDividend.Classical.runningSup_terminal_extended_clock_discount_upper X ω q (b + (N : ℝ) * h) h hq hbN hh
      (u N) t (hu N le_rfl) ht)

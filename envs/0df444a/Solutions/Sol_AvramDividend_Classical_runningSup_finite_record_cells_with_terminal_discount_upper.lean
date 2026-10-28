-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_finite_record_cells_with_terminal_discount_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:22:48.494971+00:00
-- url     : https://prove2.me/submissions/3a336a98-0f7e-4041-b7f5-7bddb715899f

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_N_record_cells_discount_upper_bound
import Theorems.Thm_AvramDividend_Classical_runningSup_terminal_extended_clock_stopped_discount_upper
import Theorems.Thm_AvramDividend_Classical_stopped_lintegral_Ioc_adjacent_add

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
  let μ : Measure ℝ := dividendMeasure (runningSup X) ω
  let W : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (Real.exp (-(q * r)))
  have hPrefix :=
    runningSup_N_record_cells_discount_upper_bound
      X ω τ q hq b h hb hh N u hu hord hSurvive
  have hlevel : b + ((N + 1 : ℕ) : ℝ) * h =
      (b + (N : ℝ) * h) + h := by
    push_cast
    ring
  have hbn : 0 ≤ b + (N : ℝ) * h :=
    add_nonneg hb (mul_nonneg (Nat.cast_nonneg N) hh)
  have huN : (u N : ℝ≥0∞) =
      (⨅ (r : ℝ≥0)
        (_ : b + (N : ℝ) * h < X.X r ω), (r : ℝ≥0∞)) :=
    hu N (le_refl N)
  have hnext : (t : ℝ≥0∞) ≤
      (⨅ (r : ℝ≥0)
        (_ : (b + (N : ℝ) * h) + h < X.X r ω),
        (r : ℝ≥0∞)) := by
    rw [← hlevel]
    exact ht
  have hTail :=
    runningSup_terminal_extended_clock_stopped_discount_upper
      X ω τ q (b + (N : ℝ) * h) h hq hbn hh (u N) t huN hnext
  have hAdd :=
    stopped_lintegral_Ioc_adjacent_add
      μ (paymentTimes τ) W (u 0 : ℝ) (u N : ℝ) (t : ℝ)
      hstart hNt
  change
      (∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc (u 0 : ℝ) (t : ℝ)
        then W r else 0 ∂μ) ≤
      ∑ k ∈ Finset.range (N + 1),
        W (u k : ℝ) * ENNReal.ofReal h
  rw [Finset.sum_range_succ, hAdd]
  exact add_le_add hPrefix hTail

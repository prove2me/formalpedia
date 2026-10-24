-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_stopped_firstRecord_fin_grid_discount_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:52:21.750902+00:00
-- url     : https://prove2.me/submissions/d7d4a406-7d9f-4aa8-9fb0-5019e7a76c8b

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_stopped_lintegral_Ioc_partition_fin
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_firstRecord_step_discount_bounds
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators Classical
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (b h : ℝ) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (n : ℕ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (hpass : ∀ i : ℕ, i ≤ n →
      (t i : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b + (i : ℝ) * h < X.X r ω),
        (r : ℝ≥0∞)))
    (hSurvive : ENNReal.ofReal (t n : ℝ) < τ) :
    (∑ i ∈ Finset.range n,
      ENNReal.ofReal (Real.exp (-(q * (t (i + 1) : ℝ)))) *
        ENNReal.ofReal h) ≤ (∫⁻ r in paymentTimes τ,
      if r ∈ Set.Ioc (t 0 : ℝ) (t n : ℝ)
      then ENNReal.ofReal (Real.exp (-(q * r))) else 0
      ∂(dividendMeasure (runningSup X) ω)) ∧ (∫⁻ r in paymentTimes τ,
      if r ∈ Set.Ioc (t 0 : ℝ) (t n : ℝ)
      then ENNReal.ofReal (Real.exp (-(q * r))) else 0
      ∂(dividendMeasure (runningSup X) ω)) ≤ (∑ i ∈ Finset.range n,
      ENNReal.ofReal (Real.exp (-(q * (t i : ℝ)))) *
        ENNReal.ofReal h) := by
  classical
  let I (i : ℕ) : ℝ≥0∞ :=
    ∫⁻ r in paymentTimes τ,
      if r ∈ Set.Ioc (t i : ℝ) (t (i + 1) : ℝ)
      then ENNReal.ofReal (Real.exp (-(q * r))) else 0
      ∂(dividendMeasure (runningSup X) ω)
  have htR : Monotone (fun i : ℕ => (t i : ℝ)) := by
    intro i j hij
    exact_mod_cast ht hij
  have hstep (i : ℕ) (hi : i ∈ Finset.range n) :
      ENNReal.ofReal (Real.exp (-(q * (t (i + 1) : ℝ)))) *
        ENNReal.ofReal h ≤ I i ∧
      I i ≤ ENNReal.ofReal (Real.exp (-(q * (t i : ℝ)))) *
        ENNReal.ofReal h := by
    have hin : i < n := Finset.mem_range.mp hi
    have hbi : 0 ≤ b + (i : ℝ) * h := by positivity
    have hlevel : b + (i : ℝ) * h + h =
        b + ((i + 1 : ℕ) : ℝ) * h := by
      push_cast
      ring
    have hu := hpass i (Nat.le_of_lt hin)
    have hv := hpass (i + 1) (Nat.succ_le_of_lt hin)
    rw [← hlevel] at hv
    have hτi : ENNReal.ofReal (t (i + 1) : ℝ) < τ := by
      apply lt_of_le_of_lt _ hSurvive
      exact ENNReal.ofReal_le_ofReal (htR (Nat.succ_le_of_lt hin))
    dsimp [I]
    exact runningSup_stopped_firstRecord_step_discount_bounds
      X ω τ q hq (b + (i : ℝ) * h) h hbi hh
      (t i) (t (i + 1)) hu hv hτi
  have hpart :
      (∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc (t 0 : ℝ) (t n : ℝ)
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) =
      ∑ i ∈ Finset.range n, I i := by
    simpa only [I] using
      (stopped_lintegral_Ioc_partition_fin
        (dividendMeasure (runningSup X) ω) (paymentTimes τ)
        (fun r : ℝ => ENNReal.ofReal (Real.exp (-(q * r))))
        (fun i : ℕ => (t i : ℝ)) htR n)
  constructor
  · calc
      _ ≤ ∑ i ∈ Finset.range n, I i := by
        apply Finset.sum_le_sum
        intro i hi
        exact (hstep i hi).1
      _ = _ := hpart.symm
  · calc
      _ = ∑ i ∈ Finset.range n, I i := hpart
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        exact (hstep i hi).2

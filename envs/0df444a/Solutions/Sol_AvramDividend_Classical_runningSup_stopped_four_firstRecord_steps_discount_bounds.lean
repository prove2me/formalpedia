-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_stopped_four_firstRecord_steps_discount_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:46:19.529566+00:00
-- url     : https://prove2.me/submissions/ad7711c7-84bf-47ca-854f-e643748e5830

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_four_firstRecord_steps_discount_pair_bounds
import Theorems.Thm_AvramDividend_Classical_stopped_lintegral_Ioc_adjacent_add
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

/-- Four attained record cells bound the exact reward over one combined
half-open stopped interval by their left and right discounted sums. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (b h : ℝ) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (u v z w k : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)))
    (hv : (v : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b + h < X.X r ω), (r : ℝ≥0∞)))
    (hz : (z : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b + h + h < X.X r ω), (r : ℝ≥0∞)))
    (hw : (w : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b + h + h + h < X.X r ω), (r : ℝ≥0∞)))
    (hk : (k : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b + h + h + h + h < X.X r ω), (r : ℝ≥0∞)))
    (huv : (u : ℝ) ≤ (v : ℝ)) (hvz : (v : ℝ) ≤ (z : ℝ))
    (hzw : (z : ℝ) ≤ (w : ℝ)) (hwk : (w : ℝ) ≤ (k : ℝ))
    (hSurvive : ENNReal.ofReal (k : ℝ) < τ) :
    ((ENNReal.ofReal (Real.exp (-(q * (v : ℝ)))) * ENNReal.ofReal h +
      ENNReal.ofReal (Real.exp (-(q * (z : ℝ)))) * ENNReal.ofReal h) +
     (ENNReal.ofReal (Real.exp (-(q * (w : ℝ)))) * ENNReal.ofReal h +
      ENNReal.ofReal (Real.exp (-(q * (k : ℝ)))) * ENNReal.ofReal h) ≤
     (∫⁻ r in paymentTimes τ,
       if r ∈ Set.Ioc (u : ℝ) (k : ℝ)
       then ENNReal.ofReal (Real.exp (-(q * r))) else 0
       ∂(dividendMeasure (runningSup X) ω))) ∧
    ((∫⁻ r in paymentTimes τ,
       if r ∈ Set.Ioc (u : ℝ) (k : ℝ)
       then ENNReal.ofReal (Real.exp (-(q * r))) else 0
       ∂(dividendMeasure (runningSup X) ω)) ≤
     (ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) * ENNReal.ofReal h +
      ENNReal.ofReal (Real.exp (-(q * (v : ℝ)))) * ENNReal.ofReal h) +
     (ENNReal.ofReal (Real.exp (-(q * (z : ℝ)))) * ENNReal.ofReal h +
      ENNReal.ofReal (Real.exp (-(q * (w : ℝ)))) * ENNReal.ofReal h)) := by
  have hPair :=
    runningSup_stopped_four_firstRecord_steps_discount_pair_bounds
      X ω τ q hq b h hb hh u v z w k hu hv hz hw hk huv hvz hzw hwk hSurvive
  have hAdd :
      (∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc (u : ℝ) (k : ℝ)
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) =
      (∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc (u : ℝ) (z : ℝ)
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) +
      (∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc (z : ℝ) (k : ℝ)
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) :=
    stopped_lintegral_Ioc_adjacent_add
      (dividendMeasure (runningSup X) ω) (paymentTimes τ)
      (fun r => ENNReal.ofReal (Real.exp (-(q * r))))
      (u : ℝ) (z : ℝ) (k : ℝ)
      (le_trans huv hvz) (le_trans hzw hwk)
  constructor
  · rw [hAdd]
    exact hPair.1
  · rw [hAdd]
    exact hPair.2

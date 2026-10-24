-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_stopped_four_firstRecord_steps_discount_pair_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:36:14.266332+00:00
-- url     : https://prove2.me/submissions/bc931307-c9b6-4336-93b5-696b5c27f68b

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_two_firstRecord_steps_discount_bounds
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

/-- Four successive attained record steps split into two stopped, discounted
Stieltjes windows. This is the four-cell bound before interval aggregation. -/
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
       if r ∈ Set.Ioc (u : ℝ) (z : ℝ)
       then ENNReal.ofReal (Real.exp (-(q * r))) else 0
       ∂(dividendMeasure (runningSup X) ω)) +
     (∫⁻ r in paymentTimes τ,
       if r ∈ Set.Ioc (z : ℝ) (k : ℝ)
       then ENNReal.ofReal (Real.exp (-(q * r))) else 0
       ∂(dividendMeasure (runningSup X) ω))) ∧
    ((∫⁻ r in paymentTimes τ,
       if r ∈ Set.Ioc (u : ℝ) (z : ℝ)
       then ENNReal.ofReal (Real.exp (-(q * r))) else 0
       ∂(dividendMeasure (runningSup X) ω)) +
     (∫⁻ r in paymentTimes τ,
       if r ∈ Set.Ioc (z : ℝ) (k : ℝ)
       then ENNReal.ofReal (Real.exp (-(q * r))) else 0
       ∂(dividendMeasure (runningSup X) ω)) ≤
     (ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) * ENNReal.ofReal h +
      ENNReal.ofReal (Real.exp (-(q * (v : ℝ)))) * ENNReal.ofReal h) +
     (ENNReal.ofReal (Real.exp (-(q * (z : ℝ)))) * ENNReal.ofReal h +
      ENNReal.ofReal (Real.exp (-(q * (w : ℝ)))) * ENNReal.ofReal h)) := by
  have hzk : (z : ℝ) ≤ (k : ℝ) := le_trans hzw hwk
  have hSurviveZ : ENNReal.ofReal (z : ℝ) < τ :=
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hzk) hSurvive
  have hb2 : 0 ≤ b + h + h :=
    add_nonneg (add_nonneg hb hh) hh
  have hLeft :=
    runningSup_stopped_two_firstRecord_steps_discount_bounds
      X ω τ q hq b h hb hh u v z hu hv hz huv hvz hSurviveZ
  have hRight :=
    runningSup_stopped_two_firstRecord_steps_discount_bounds
      X ω τ q hq (b + h + h) h hb2 hh z w k hz hw hk hzw hwk hSurvive
  exact ⟨add_le_add hLeft.1 hRight.1,
    add_le_add hLeft.2 hRight.2⟩

-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_stopped_two_firstRecord_steps_discount_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T09:40:40.259877+00:00
-- url     : https://prove2.me/submissions/a245904e-e315-426f-a052-20b87697be2d

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_lintegral_Ioc_adjacent_add
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_firstRecord_step_discount_bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (b h : ℝ) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (u v z : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)))
    (hv : (v : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b + h < X.X r ω), (r : ℝ≥0∞)))
    (hz : (z : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b + h + h < X.X r ω), (r : ℝ≥0∞)))
    (huv : (u : ℝ) ≤ (v : ℝ))
    (hvz : (v : ℝ) ≤ (z : ℝ))
    (hSurvive : ENNReal.ofReal (z : ℝ) < τ) :
    (ENNReal.ofReal (Real.exp (-(q * (v : ℝ)))) * ENNReal.ofReal h +
     ENNReal.ofReal (Real.exp (-(q * (z : ℝ)))) * ENNReal.ofReal h ≤ ∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc (u : ℝ) (z : ℝ)
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ∧
    (∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc (u : ℝ) (z : ℝ)
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω) ≤ ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) * ENNReal.ofReal h +
     ENNReal.ofReal (Real.exp (-(q * (v : ℝ)))) * ENNReal.ofReal h) := by
  let μ : Measure ℝ := dividendMeasure (runningSup X) ω
  let ν : Measure ℝ := μ.restrict (paymentTimes τ)
  let W : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (Real.exp (-(q * r)))
  let R : ℝ → ℝ → ℝ≥0∞ := fun a c =>
    ∫⁻ r in paymentTimes τ,
      if r ∈ Set.Ioc a c then W r else 0 ∂μ
  have hRepr (a c : ℝ) :
      R a c = ∫⁻ r in Set.Ioc a c, W r ∂ν := by
    change (∫⁻ r, if r ∈ Set.Ioc a c then W r else 0 ∂ν) =
      ∫⁻ r in Set.Ioc a c, W r ∂ν
    have hfun :
        (fun r : ℝ => if r ∈ Set.Ioc a c then W r else 0) =
        (Set.Ioc a c).indicator W := by
      funext r
      by_cases hr : r ∈ Set.Ioc a c
      · simp [hr, Set.indicator_of_mem hr]
      · simp [hr, Set.indicator_of_notMem hr]
    rw [hfun]
    exact lintegral_indicator measurableSet_Ioc W
  have hAdd : R (u : ℝ) (z : ℝ) =
      R (u : ℝ) (v : ℝ) + R (v : ℝ) (z : ℝ) := by
    calc
      R (u : ℝ) (z : ℝ) =
          ∫⁻ r in Set.Ioc (u : ℝ) (z : ℝ), W r ∂ν :=
        hRepr _ _
      _ = (∫⁻ r in Set.Ioc (u : ℝ) (v : ℝ), W r ∂ν) +
          (∫⁻ r in Set.Ioc (v : ℝ) (z : ℝ), W r ∂ν) :=
        lintegral_Ioc_adjacent_add ν W _ _ _ huv hvz
      _ = R (u : ℝ) (v : ℝ) + R (v : ℝ) (z : ℝ) := by
        rw [← hRepr (u : ℝ) (v : ℝ),
          ← hRepr (v : ℝ) (z : ℝ)]
  have hBefore : ENNReal.ofReal (v : ℝ) < τ :=
    lt_of_le_of_lt (ENNReal.ofReal_mono hvz) hSurvive
  have hFirst := runningSup_stopped_firstRecord_step_discount_bounds
    X ω τ q hq b h hb hh u v hu hv hBefore
  have hSecond := runningSup_stopped_firstRecord_step_discount_bounds
    X ω τ q hq (b + h) h (add_nonneg hb hh) hh v z hv hz hSurvive
  have hLow : ENNReal.ofReal (Real.exp (-(q * (v : ℝ)))) * ENNReal.ofReal h +
     ENNReal.ofReal (Real.exp (-(q * (z : ℝ)))) * ENNReal.ofReal h ≤
      R (u : ℝ) (v : ℝ) + R (v : ℝ) (z : ℝ) :=
    add_le_add hFirst.1 hSecond.1
  have hUp :
      R (u : ℝ) (v : ℝ) + R (v : ℝ) (z : ℝ) ≤
      ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) * ENNReal.ofReal h +
     ENNReal.ofReal (Real.exp (-(q * (v : ℝ)))) * ENNReal.ofReal h :=
    add_le_add hFirst.2 hSecond.2
  constructor
  · change ENNReal.ofReal (Real.exp (-(q * (v : ℝ)))) * ENNReal.ofReal h +
     ENNReal.ofReal (Real.exp (-(q * (z : ℝ)))) * ENNReal.ofReal h ≤ R (u : ℝ) (z : ℝ)
    rw [hAdd]
    exact hLow
  · change R (u : ℝ) (z : ℝ) ≤ ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) * ENNReal.ofReal h +
     ENNReal.ofReal (Real.exp (-(q * (v : ℝ)))) * ENNReal.ofReal h
    rw [hAdd]
    exact hUp

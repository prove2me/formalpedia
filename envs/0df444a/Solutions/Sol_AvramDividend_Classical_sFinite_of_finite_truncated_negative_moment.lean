-- Prove2me | solution 1 for AvramDividend.Classical.sFinite_of_finite_truncated_negative_moment
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T18:15:54.302424+00:00
-- url     : https://prove2.me/submissions/7e15c9d3-12b6-463b-a1cd-5e8eb12aea3e

import Mathlib
open MeasureTheory Set
open scoped ENNReal

/-- A measure carried by the negative half-line is s-finite when the truncated negative magnitude has finite integral. -/
theorem solution
    (ν : Measure ℝ)
    (hIci : ν (Ici (0 : ℝ)) = 0)
    (hfin : (∫⁻ y in Iio (0 : ℝ), ENNReal.ofReal (min (-y) 1) ∂ν) < ⊤) :
    SFinite ν := by
  set f : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (min (-y) 1) with hf
  have hae : ∀ᵐ x ∂ν, x ∈ Iio (0 : ℝ) := by
    rw [ae_iff]
    have : {a : ℝ | ¬ a ∈ Iio 0} = Ici 0 := by ext; simp
    rw [this]; exact hIci
  have hν : ν.restrict (Iio 0) = ν := Measure.restrict_eq_self_of_ae_mem hae
  have : IsFiniteMeasure ((ν.restrict (Iio 0)).withDensity f) :=
    isFiniteMeasure_withDensity hfin.ne
  have hmeas : Measurable f := by fun_prop
  have hpos : ∀ᵐ x ∂(ν.restrict (Iio 0)), f x ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    simp only [hf, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact lt_min (by simpa using hx) one_pos
  have htop : ∀ᵐ x ∂(ν.restrict (Iio 0)), f x ≠ ∞ := by
    filter_upwards with x using ENNReal.ofReal_ne_top
  have := withDensity_inv_same hmeas hpos htop
  rw [← hν, ← this]
  infer_instance

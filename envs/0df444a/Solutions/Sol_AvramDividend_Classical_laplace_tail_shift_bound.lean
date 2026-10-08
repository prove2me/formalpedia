-- Prove2me | solution 1 for AvramDividend.Classical.laplace_tail_shift_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T06:23:07.621338+00:00
-- url     : https://prove2.me/submissions/310e863d-849d-43db-a999-bdbed089a86c

import Mathlib

open MeasureTheory Filter Set Topology

theorem solution
    (W : ℝ → ℝ) (a β0 β : ℝ)
    (hβ : β0 ≤ β)
    (hW : ∀ x : ℝ, x ∈ Ioi a → 0 ≤ W x)
    (h0 : IntegrableOn (fun x : ℝ => Real.exp (-β0 * x) * W x) (Ioi a))
    (h1 : IntegrableOn (fun x : ℝ => Real.exp (-β * x) * W x) (Ioi a)) :
    (∫ x in Ioi a, Real.exp (-β * x) * W x) ≤
      Real.exp (-(β - β0) * a) *
        ∫ x in Ioi a, Real.exp (-β0 * x) * W x := by
  have hc : 0 ≤ β - β0 := sub_nonneg.mpr hβ
  have hpoint :
      ∀ x : ℝ, x ∈ Ioi a →
        Real.exp (-β * x) * W x ≤
          Real.exp (-(β - β0) * a) *
            (Real.exp (-β0 * x) * W x) := by
    intro x hx
    have hlin :
        -(β - β0) * x ≤ -(β - β0) * a := by
      have hmul := mul_le_mul_of_nonneg_left (le_of_lt hx) hc
      nlinarith
    have hexp :
        Real.exp (-(β - β0) * x) ≤
          Real.exp (-(β - β0) * a) :=
      Real.exp_le_exp.mpr hlin
    have hbase : 0 ≤ Real.exp (-β0 * x) * W x :=
      mul_nonneg (Real.exp_pos _).le (hW x hx)
    calc
      Real.exp (-β * x) * W x =
          Real.exp (-(β - β0) * x) *
            (Real.exp (-β0 * x) * W x) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-(β - β0) * a) *
            (Real.exp (-β0 * x) * W x) :=
        mul_le_mul_of_nonneg_right hexp hbase
  calc
    (∫ x in Ioi a, Real.exp (-β * x) * W x) ≤
        ∫ x in Ioi a,
          Real.exp (-(β - β0) * a) *
            (Real.exp (-β0 * x) * W x) := by
      exact integral_mono_ae h1
        (h0.const_mul (Real.exp (-(β - β0) * a))) <| by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          exact hpoint x hx
    _ = Real.exp (-(β - β0) * a) *
          ∫ x in Ioi a, Real.exp (-β0 * x) * W x := by
      rw [integral_const_mul]

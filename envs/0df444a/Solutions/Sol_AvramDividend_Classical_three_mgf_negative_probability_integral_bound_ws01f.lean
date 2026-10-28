-- Prove2me | solution 1 for AvramDividend.Classical.three_mgf_negative_probability_integral_bound_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:37:14.328989+00:00
-- url     : https://prove2.me/submissions/92bf2ceb-d98a-465d-874a-684197e63960

import Theorems.Thm_AvramDividend_Classical_exp_three_scale_negative_indicator_ws01f

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

open MeasureTheory Filter Set
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : Measurable Y)
    (r : ℝ) (hr : 1 ≤ r)
    (h1 : Integrable (fun ω => Real.exp (Y ω)) μ)
    (hs : Integrable (fun ω => Real.exp (Y ω / r)) μ)
    (h2 : Integrable (fun ω => Real.exp (2 * Y ω)) μ) :
    (∫ ω, (Real.exp (Y ω) - 1) ∂μ) ≤
      r ^ 2 * (∫ ω, (Real.exp (Y ω / r) - 1) ∂μ) +
      (∫ ω, (Real.exp (2 * Y ω) - 1) ∂μ) / r +
      (r ^ 2 + 1 / r) * μ.real {ω | Y ω < 0} := by
  let S : Set Ω := {ω | Y ω < 0}
  have hS : MeasurableSet S := measurableSet_lt hY measurable_const
  have hc : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const _
  have hleft : Integrable (fun ω => Real.exp (Y ω) - 1) μ := h1.sub hc
  have hsmall : Integrable (fun ω => Real.exp (Y ω / r) - 1) μ := hs.sub hc
  have htwo : Integrable (fun ω => Real.exp (2 * Y ω) - 1) μ := h2.sub hc
  have hfun :
      (fun ω : Ω => if Y ω < 0 then (1 : ℝ) else 0) =
      S.indicator (fun _ : Ω => (1 : ℝ)) := by
    funext ω
    by_cases hh : Y ω < 0 <;> simp [S, Set.indicator, hh]
  have hi : Integrable (fun ω => if Y ω < 0 then (1 : ℝ) else 0) μ := by
    rw [hfun]
    exact hc.indicator hS
  have hfirst : Integrable
      (fun ω => r ^ 2 * (Real.exp (Y ω / r) - 1)) μ :=
    hsmall.const_mul _
  have hsecond : Integrable
      (fun ω => (Real.exp (2 * Y ω) - 1) / r) μ :=
    htwo.div_const _
  have hthird : Integrable
      (fun ω => (r ^ 2 + 1 / r) *
        (if Y ω < 0 then (1 : ℝ) else 0)) μ :=
    hi.const_mul _
  have hright : Integrable
      (fun ω => r ^ 2 * (Real.exp (Y ω / r) - 1) +
        (Real.exp (2 * Y ω) - 1) / r +
        (r ^ 2 + 1 / r) *
          (if Y ω < 0 then (1 : ℝ) else 0)) μ :=
    (hfirst.add hsecond).add hthird
  have hmono :
      (∫ ω, (Real.exp (Y ω) - 1) ∂μ) ≤
      (∫ ω, r ^ 2 * (Real.exp (Y ω / r) - 1) +
        (Real.exp (2 * Y ω) - 1) / r +
        (r ^ 2 + 1 / r) *
          (if Y ω < 0 then (1 : ℝ) else 0) ∂μ) := by
    apply integral_mono_ae hleft hright
    exact Filter.Eventually.of_forall
      (fun ω => exp_three_scale_negative_indicator_ws01f r (Y ω) hr)
  have heval :
      (∫ ω, (if Y ω < 0 then (1 : ℝ) else 0) ∂μ) =
        μ.real S := by
    rw [hfun, integral_indicator_const (1 : ℝ) hS]
    simp
  have hcalc :
      (∫ ω, r ^ 2 * (Real.exp (Y ω / r) - 1) +
        (Real.exp (2 * Y ω) - 1) / r +
        (r ^ 2 + 1 / r) *
          (if Y ω < 0 then (1 : ℝ) else 0) ∂μ) =
      r ^ 2 * (∫ ω, (Real.exp (Y ω / r) - 1) ∂μ) +
      (∫ ω, (Real.exp (2 * Y ω) - 1) ∂μ) / r +
      (r ^ 2 + 1 / r) * μ.real S := by
    calc
      _ = (∫ ω, r ^ 2 * (Real.exp (Y ω / r) - 1) +
            (Real.exp (2 * Y ω) - 1) / r ∂μ) +
          (∫ ω, (r ^ 2 + 1 / r) *
            (if Y ω < 0 then (1 : ℝ) else 0) ∂μ) := by
        simpa only [Pi.add_apply] using
          (integral_add (hfirst.add hsecond) hthird)
      _ = _ := by
        rw [show (∫ ω, r ^ 2 * (Real.exp (Y ω / r) - 1) +
          (Real.exp (2 * Y ω) - 1) / r ∂μ) =
          (∫ ω, r ^ 2 * (Real.exp (Y ω / r) - 1) ∂μ) +
          (∫ ω, (Real.exp (2 * Y ω) - 1) / r ∂μ) from by
            simpa only [Pi.add_apply] using (integral_add hfirst hsecond)]
        simp only [integral_const_mul, integral_div, heval]
  exact le_of_le_of_eq hmono hcalc

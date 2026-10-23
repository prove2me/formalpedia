-- Prove2me | solution 1 for AvramDividend.Classical.monotone_exp_laplace_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T20:57:41.208989+00:00
-- url     : https://prove2.me/submissions/21bbab59-4860-4ddd-b82e-37f142ec9cc0

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution
    (V : ℝ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hVnonneg : ∀ x : ℝ, 0 < x → 0 ≤ V x)
    (hmono : MonotoneOn V (Ioi (0 : ℝ)))
    (hLap : ∀ θ : ℝ, 0 < θ →
      IntegrableOn (fun y : ℝ => Real.exp (-(θ * y)) * V y) (Ioi 0) volume ∧
      (∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * V y ∂volume) ≤ A / θ) :
    ∀ x : ℝ, 0 < x → V x ≤ Real.exp 2 * A := by
  intro x hx
  have hxinv : 0 < x⁻¹ := inv_pos.mpr hx
  obtain ⟨hI, hU⟩ := hLap x⁻¹ hxinv
  let f : ℝ → ℝ := fun y => Real.exp (-(x⁻¹ * y)) * V y
  have hfi : IntegrableOn f (Ioi (0 : ℝ)) volume := hI
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f := by
    filter_upwards [ae_restrict_mem isOpen_Ioi.measurableSet] with y hy
    exact mul_nonneg (le_of_lt (Real.exp_pos _)) (hVnonneg y hy)
  have hxle : x ≤ 2 * x := by linarith
  have hseg :
      (∫ y in x..(2*x), f y ∂volume) ≤
        (∫ y in Ioi (0 : ℝ), f y ∂volume) := by
    rw [intervalIntegral.integral_of_le hxle]
    apply setIntegral_mono_set hfi hnonneg
    exact Filter.Eventually.of_forall (fun y hy =>
      lt_trans hx hy.1)
  have hpoint : ∀ y ∈ Icc x (2*x),
      Real.exp (-2) * V x ≤ f y := by
    intro y hy
    have hypos : 0 < y := lt_of_lt_of_le hx hy.1
    have hVy : V x ≤ V y :=
      hmono (mem_Ioi.mpr hx) (mem_Ioi.mpr hypos) hy.1
    have hquot : x⁻¹ * y ≤ 2 := by
      have hdiv : y / x ≤ 2 :=
        (div_le_iff₀ hx).mpr (by nlinarith [hy.2])
      simpa [div_eq_mul_inv, mul_comm] using hdiv
    have hexp : Real.exp (-2) ≤ Real.exp (-(x⁻¹*y)) :=
      Real.exp_le_exp.mpr (by linarith)
    calc
      Real.exp (-2) * V x ≤ Real.exp (-2) * V y :=
        mul_le_mul_of_nonneg_left hVy (le_of_lt (Real.exp_pos _))
      _ ≤ Real.exp (-(x⁻¹*y)) * V y :=
        mul_le_mul_of_nonneg_right hexp (hVnonneg y hypos)
  have hminor :
      x * (Real.exp (-2) * V x) ≤ (∫ y in x..(2*x), f y ∂volume) := by
    have hfi_interval : IntervalIntegrable f volume x (2*x) := by
      apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hxle).2
      exact hfi.mono_set (by
        intro y hy
        exact lt_trans hx hy.1)
    have h := intervalIntegral.integral_mono_on
      (a := x) (b := 2*x)
      (f := fun _ : ℝ => Real.exp (-2) * V x)
      (g := f) hxle intervalIntegrable_const hfi_interval hpoint
    have hd : 2*x-x = x := by ring
    simpa [intervalIntegral.integral_const, hd, smul_eq_mul, mul_left_comm] using h
  have hupper : (∫ y in Ioi (0 : ℝ), f y ∂volume) ≤ A*x := by
    simpa [f, div_inv_eq_mul] using hU
  have hsmall : Real.exp (-2) * V x ≤ A := by
    have hbound := le_trans hminor (le_trans hseg hupper)
    have hscaled : x * (Real.exp (-2) * V x) ≤ x * A := by
      simpa [mul_comm] using hbound
    exact le_of_mul_le_mul_left hscaled hx
  have hexp : Real.exp 2 * Real.exp (-2) = 1 := by
    rw [← Real.exp_add]
    norm_num
  calc
    V x = Real.exp 2 * (Real.exp (-2) * V x) := by
      rw [← mul_assoc, hexp, one_mul]
    _ ≤ Real.exp 2 * A :=
      mul_le_mul_of_nonneg_left hsmall (le_of_lt (Real.exp_pos _))

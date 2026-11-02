-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_integrable_signed_negative_jump_tail_DCT
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:53:26.93737+00:00
-- url     : https://prove2.me/submissions/6c079e89-8fe5-4038-934e-bd55574c0732

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped BigOperators

/-! The absolutely integrable negative-jump generator tail vanishes, even
when the signed kernel has no global polynomial first-moment envelope. -/
theorem solution (μ : Measure ℝ) (f : ℝ → ℝ)
    (hf : Measurable f)
    (hInt : IntegrableOn f (Iio (0 : ℝ)) μ) :
    Tendsto
      (fun n : ℕ =>
        ∫ y in Iio (0 : ℝ),
          if y < -(n : ℝ) then f y else 0 ∂μ)
      atTop (nhds 0) := by
  let μ' := μ.restrict (Iio (0 : ℝ))
  have hmeas (n : ℕ) :
      AEStronglyMeasurable (fun y : ℝ =>
        if y < -(n : ℝ) then f y else 0) μ' := by
    have hs : MeasurableSet {y : ℝ | y < -(n : ℝ)} :=
      measurableSet_Iio
    exact (hf.ite hs measurable_const).aestronglyMeasurable
  have hbound (n : ℕ) :
      ∀ᵐ y ∂μ', ‖if y < -(n : ℝ) then f y else 0‖ ≤ ‖f y‖ := by
    filter_upwards [] with y
    split_ifs <;> simp
  have hpoint (y : ℝ) :
      Tendsto (fun n : ℕ => if y < -(n : ℝ) then f y else 0)
        atTop (nhds 0) := by
    obtain ⟨N, hN⟩ := exists_nat_ge (-y)
    have hevent : ∀ᶠ n : ℕ in atTop, ¬y < -(n : ℝ) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      exact not_lt.mpr (by linarith)
    have heq :
        (fun n : ℕ => if y < -(n : ℝ) then f y else 0) =ᶠ[atTop]
          fun _ => (0 : ℝ) := by
      filter_upwards [hevent] with n hn
      simp [hn]
    exact tendsto_const_nhds.congr' heq.symm
  simpa only [integral_zero, μ'] using tendsto_integral_of_dominated_convergence
    (fun y => ‖f y‖) hmeas hInt.norm hbound
    (Filter.Eventually.of_forall hpoint)

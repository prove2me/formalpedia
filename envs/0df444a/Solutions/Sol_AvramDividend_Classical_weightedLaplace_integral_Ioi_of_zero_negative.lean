-- Prove2me | solution 1 for AvramDividend.Classical.weightedLaplace_integral_Ioi_of_zero_negative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:16:10.984822+00:00
-- url     : https://prove2.me/submissions/65eeb45a-9723-4c97-8171-4273eabcd104

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution
    (f : ℝ → ℝ) (θ : ℝ)
    (hf : ∀ x : ℝ, x < 0 → f x = 0) :
    (∫ x : ℝ, Real.exp (-(θ * x)) * f x) =
      ∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * f x := by
  have hzero :
      ∀ x ∈ (Ici (0 : ℝ))ᶜ,
        Real.exp (-(θ * x)) * f x = 0 := by
    intro x hx
    have hxneg : x < 0 := by simpa only [mem_compl_iff, mem_Ici, not_le] using hx
    simp [hf x hxneg]
  calc
    (∫ x : ℝ, Real.exp (-(θ * x)) * f x) =
        ∫ x in Ici (0 : ℝ), Real.exp (-(θ * x)) * f x :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ = ∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * f x := by
      change
        (∫ x : ℝ, Real.exp (-(θ * x)) * f x
          ∂(volume.restrict (Ici (0 : ℝ)))) =
        (∫ x : ℝ, Real.exp (-(θ * x)) * f x
          ∂(volume.restrict (Ioi (0 : ℝ))))
      rw [MeasureTheory.restrict_Ioi_eq_restrict_Ici]

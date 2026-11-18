-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_finite_mark_intensity_normalised_Laplace_coefficient_20261118
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T03:05:45.347132+00:00
-- url     : https://prove2.me/submissions/5bb27bf2-fc83-4dac-a5ce-882877846fdf

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
open MeasureTheory Set
noncomputable section

theorem solution
    (ν : Measure ℝ) (B : Set ℝ) (θ : ℝ)
    (hOne : IntegrableOn (fun _ : ℝ => (1 : ℝ)) B ν)
    (hExp : IntegrableOn (fun y : ℝ => Real.exp (θ * y)) B ν)
    (hBound : ∀ᵐ y ∂ν.restrict B,
      0 ≤ Real.exp (θ * y) ∧ Real.exp (θ * y) ≤ 1)
    (hMass : 0 < (ν B).toReal)
    (T r : ℝ) (hr : r = T * (ν B).toReal) :
    ∃ m : ℝ, 0 ≤ m ∧ m ≤ 1 ∧
      r * (m - 1) = T *
        (∫ y in B, Real.exp (θ * y) - 1 ∂ν) := by
  have hone : (∫ y in B, (1 : ℝ) ∂ν) = (ν B).toReal := by
    simp [Measure.real]
  have hI0 : 0 ≤ ∫ y in B, Real.exp (θ * y) ∂ν :=
    integral_nonneg_of_ae (hBound.mono fun y hy => hy.1)
  have hI1 : (∫ y in B, Real.exp (θ * y) ∂ν) ≤ (ν B).toReal := by
    rw [← hone]
    exact integral_mono_ae hExp hOne (hBound.mono fun y hy => hy.2)
  refine ⟨(∫ y in B, Real.exp (θ * y) ∂ν) / (ν B).toReal, div_nonneg hI0 hMass.le,
    (div_le_one hMass).2 hI1, ?_⟩
  rw [integral_sub hExp hOne, hone, hr]
  field_simp

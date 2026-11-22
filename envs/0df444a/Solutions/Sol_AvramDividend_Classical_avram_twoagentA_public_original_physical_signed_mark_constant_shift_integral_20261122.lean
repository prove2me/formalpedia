-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_public_original_physical_signed_mark_constant_shift_integral_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:06:52.405498+00:00
-- url     : https://prove2.me/submissions/8f42a5f3-070c-4b2b-a153-5b2f3f286c51

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (μ : Measure (ℝ≥0 × ℝ)) (S : Set (ℝ≥0 × ℝ)) (c : ℝ)
    (hFin : μ S < ⊤)
    (hInt : IntegrableOn (fun p : ℝ≥0 × ℝ => p.2) S μ) :
    (∫ p in S, p.2 + c ∂μ) =
      (∫ p in S, p.2 ∂μ) + c * (μ S).toReal := by
  classical
  have hConst : IntegrableOn (fun _ : ℝ≥0 × ℝ => c) S μ := by
    apply integrableOn_const
    · exact ne_of_lt hFin
    · simp
  calc
    (∫ p in S, p.2 + c ∂μ) =
        (∫ p in S, p.2 ∂μ) +
          (∫ p in S, c ∂μ) := integral_add hInt hConst
    _ = (∫ p in S, p.2 ∂μ) + c * (μ S).toReal := by
      simp [MeasureTheory.integral_const, Measure.real, mul_comm]

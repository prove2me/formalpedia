-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_budget_positive_error_expected_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:37:59.809585+00:00
-- url     : https://prove2.me/submissions/3a82055f-195e-488e-9136-59d1ff40c47b

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
noncomputable section

/-- A nonnegative payoff bounded by a centred corrected budget forces
positive approximation error to pay any negative drift-budget deficit. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (c : ℝ) (F M B Err : Ω → ℝ)
    (hF : ∀ᵐ ω ∂P, 0 ≤ F ω)
    (hM : Integrable M P) (hM0 : (∫ ω, M ω ∂P) = 0)
    (hB : Integrable B P)
    (hErr : Integrable (fun ω => max (Err ω) 0) P)
    (hBudget : ∀ᵐ ω ∂P,
      F ω ≤ c + M ω + B ω + max (Err ω) 0) :
    -(∫ ω, B ω ∂P) - c ≤
      (∫ ω, max (Err ω) 0 ∂P) := by
  have hPoint : ∀ᵐ ω ∂P,
      0 ≤ c + M ω + B ω + max (Err ω) 0 := by
    filter_upwards [hF, hBudget] with ω hFω hBudω
    linarith
  have hConst : Integrable (fun _ : Ω => c) P := integrable_const _
  have hNonneg :
      0 ≤ ∫ ω, c + M ω + B ω + max (Err ω) 0 ∂P :=
    integral_nonneg_of_ae hPoint
  have hSplit :
      (∫ ω, c + M ω + B ω + max (Err ω) 0 ∂P) =
        c + (∫ ω, M ω ∂P) + (∫ ω, B ω ∂P) +
          (∫ ω, max (Err ω) 0 ∂P) := by
    calc
      _ = (∫ ω, c + M ω + B ω ∂P) +
          (∫ ω, max (Err ω) 0 ∂P) :=
          integral_add ((hConst.add hM).add hB) hErr
      _ = (∫ ω, c + M ω ∂P) + (∫ ω, B ω ∂P) +
          (∫ ω, max (Err ω) 0 ∂P) := by
          rw [show (∫ ω, c + M ω + B ω ∂P) =
              (∫ ω, c + M ω ∂P) + (∫ ω, B ω ∂P) from by
                simpa only [Pi.add_apply] using (integral_add (hConst.add hM) hB)]
      _ = c + (∫ ω, M ω ∂P) + (∫ ω, B ω ∂P) +
          (∫ ω, max (Err ω) 0 ∂P) := by
          rw [show (∫ ω, c + M ω ∂P) =
              (∫ ω, c ∂P) + (∫ ω, M ω ∂P) from by
                simpa only [Pi.add_apply] using (integral_add hConst hM)]
          simp
  rw [hSplit, hM0] at hNonneg
  linarith

-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_bounded_Hessian_weight_square_integrable_from_unweighted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:48:41.380063+00:00
-- url     : https://prove2.me/submissions/bdee2d4a-b16e-4c6e-b00e-c39ba989c8ae

import Mathlib.MeasureTheory.Function.L1Space.Integrable
open MeasureTheory Filter
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (H R : Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hBound : ∀ ω, |H ω| ≤ K)
    (hR : Integrable (fun ω => R ω ^ 2) P)
    (hMeas : AEStronglyMeasurable (fun ω => (H ω * R ω) ^ 2) P) :
    Integrable (fun ω => (H ω * R ω) ^ 2) P := by
  apply Integrable.mono' (hR.const_mul (K ^ 2)) hMeas
  filter_upwards [] with ω
  have hs : H ω ^ 2 ≤ K ^ 2 := by
    nlinarith [abs_nonneg (H ω), sq_abs (H ω),
      mul_nonneg (sub_nonneg.mpr (hBound ω))
        (add_nonneg hK (abs_nonneg (H ω)))]
  have hp : (H ω * R ω) ^ 2 ≤ K ^ 2 * R ω ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg (R ω))]
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (H ω * R ω))] using hp

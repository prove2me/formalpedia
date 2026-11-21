-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_bounded_random_Hessian_weight_L2_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:16:05.401017+00:00
-- url     : https://prove2.me/submissions/e8129d1e-6899-4692-a100-0a36b8e15ccb

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (H R : Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hBound : ∀ ω, |H ω| ≤ K)
    (hR : Integrable (fun ω => R ω ^ 2) P)
    (hHR : Integrable (fun ω => (H ω * R ω) ^ 2) P) :
    (∫ ω, (H ω * R ω) ^ 2 ∂P) ≤
      K ^ 2 * (∫ ω, R ω ^ 2 ∂P) := by
  have hpoint : ∀ ω, (H ω * R ω) ^ 2 ≤ K ^ 2 * R ω ^ 2 := by
    intro ω
    have ha := hBound ω
    have hnonneg : 0 ≤ |H ω| := abs_nonneg _
    have hsq : (H ω) ^ 2 ≤ K ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ha)
        (add_nonneg hK hnonneg), sq_abs (H ω)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hsq) (sq_nonneg (R ω))]
  calc
    (∫ ω, (H ω * R ω) ^ 2 ∂P) ≤
        ∫ ω, K ^ 2 * R ω ^ 2 ∂P := by
          exact integral_mono_ae hHR (hR.const_mul _) (Filter.Eventually.of_forall hpoint)
    _ = K ^ 2 * (∫ ω, R ω ^ 2 ∂P) := by
          rw [integral_const_mul]

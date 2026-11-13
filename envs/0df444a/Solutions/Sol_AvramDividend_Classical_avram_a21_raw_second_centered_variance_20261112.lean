-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_raw_second_centered_variance_20261112
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:21:42.093384+00:00
-- url     : https://prove2.me/submissions/bceb99bb-222f-4484-ac01-904ffcd06a72

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-- Real raw first and second moments yield the centred second moment. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (J : Ω → ℝ) (r q : ℝ)
    (hJ : Integrable J P)
    (hJ2 : Integrable (fun ω => (J ω) ^ 2) P)
    (hFirst : (∫ ω, J ω ∂P) = r)
    (hSecond : (∫ ω, (J ω) ^ 2 ∂P) = r ^ 2 + q) :
    (∫ ω, (J ω - r) ^ 2 ∂P) = q := by
  have hLinear : Integrable (fun ω => 2 * r * J ω) P :=
    hJ.const_mul _
  have hConst : Integrable (fun _ : Ω => r ^ 2) P :=
    integrable_const _
  have hAdd :
      (∫ ω, (J ω) ^ 2 - 2 * r * J ω + r ^ 2 ∂P) =
      (∫ ω, (J ω) ^ 2 - 2 * r * J ω ∂P) +
      (∫ _ : Ω, r ^ 2 ∂P) := by
    simpa only [Pi.add_apply, Pi.sub_apply] using
      (integral_add (hJ2.sub hLinear) hConst)
  have hSub :
      (∫ ω, (J ω) ^ 2 - 2 * r * J ω ∂P) =
      (∫ ω, (J ω) ^ 2 ∂P) -
      (∫ ω, 2 * r * J ω ∂P) := by
    simpa only [Pi.sub_apply] using (integral_sub hJ2 hLinear)
  calc
    _ = (∫ ω, (J ω) ^ 2 - 2 * r * J ω + r ^ 2 ∂P) := by
      apply integral_congr_ae
      filter_upwards [] with ω
      ring
    _ = (∫ ω, (J ω) ^ 2 - 2 * r * J ω ∂P) +
        (∫ _ : Ω, r ^ 2 ∂P) := hAdd
    _ = ((∫ ω, (J ω) ^ 2 ∂P) -
        (∫ ω, 2 * r * J ω ∂P)) + r ^ 2 := by
      rw [hSub]
      simp
    _ = q := by
      rw [integral_const_mul, hFirst, hSecond]
      ring

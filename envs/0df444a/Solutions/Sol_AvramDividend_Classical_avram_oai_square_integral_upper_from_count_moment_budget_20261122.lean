-- Prove2me | solution 1 for AvramDividend.Classical.avram_oai_square_integral_upper_from_count_moment_budget_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:06:37.15643+00:00
-- url     : https://prove2.me/submissions/76522e4c-53b6-42de-a2a9-c93197f02d9d

import Mathlib
open MeasureTheory
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (J N : Ω → ℝ) (c R : ℝ)
    (hJ2 : Integrable (fun ω => (J ω) ^ 2) P)
    (hN2 : Integrable (fun ω => (N ω) ^ 2) P)
    (hNBound : (∫ ω, (N ω) ^ 2 ∂P) ≤ R)
    (hNonneg : ∀ᵐ ω ∂P, 0 ≤ N ω)
    (hDom : ∀ᵐ ω ∂P, |J ω| ≤ N ω + |c|) :
    (∫ ω, (J ω) ^ 2 ∂P) ≤ 2 * R + 2 * c ^ 2  := by
  have hBound : ∀ᵐ ω ∂P,
      (J ω) ^ 2 ≤ 2 * (N ω) ^ 2 + 2 * c ^ 2 := by
    filter_upwards [hDom, hNonneg] with ω hd hn
    have hd0 : 0 ≤ N ω + |c| - |J ω| := sub_nonneg.mpr hd
    have hd1 : 0 ≤ N ω + |c| + |J ω| := by positivity
    nlinarith [mul_nonneg hd0 hd1,
      sq_nonneg (N ω - |c|), sq_abs (J ω), sq_abs c]
  have hMaj : Integrable (fun ω => 2 * (N ω) ^ 2 + 2 * c ^ 2) P :=
    (hN2.const_mul 2).add (integrable_const (2 * c ^ 2))
  have hi := integral_mono_ae hJ2 hMaj hBound
  calc
    (∫ ω, (J ω) ^ 2 ∂P) ≤
        (∫ ω, 2 * (N ω) ^ 2 + 2 * c ^ 2 ∂P) := hi
    _ = 2 * (∫ ω, (N ω) ^ 2 ∂P) + 2 * c ^ 2 := by
      rw [integral_add (hN2.const_mul 2) (integrable_const _)]
      rw [integral_const_mul]
      simp
    _ ≤ 2 * R + 2 * c ^ 2 := by linarith [hNBound]

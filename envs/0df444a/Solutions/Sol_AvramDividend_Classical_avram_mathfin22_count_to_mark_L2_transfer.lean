-- Prove2me | solution 1 for AvramDividend.Classical.avram_mathfin22_count_to_mark_L2_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:41:23.847799+00:00
-- url     : https://prove2.me/submissions/df4484c8-273a-4805-b2ae-0b43af685504

import Mathlib
open MeasureTheory Set
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (J N : Ω → ℝ) (r d : ℝ)
    (hJ : Integrable J P) (hN : Integrable N P)
    (hNcenter : Integrable (fun ω => (N ω - r) ^ 2) P)
    (hBound : ∀ᵐ ω ∂P, |J ω| ≤ N ω + |d|) :
    Integrable (fun ω => (J ω) ^ 2) P := by
  have hNmajor : Integrable
      (fun ω => 2 * (N ω - r) ^ 2 + 2 * r ^ 2) P :=
    (hNcenter.const_mul 2).add (integrable_const _)
  have hN2 : Integrable (fun ω => (N ω) ^ 2) P := by
    refine Integrable.mono' hNmajor (hN.aestronglyMeasurable.pow 2) ?_
    filter_upwards [] with ω
    have hSq : N ω ^ 2 ≤ 2 * (N ω - r) ^ 2 + 2 * r ^ 2 := by
      nlinarith [sq_nonneg (N ω - 2 * r)]
    have hNonneg : 0 ≤ 2 * (N ω - r) ^ 2 + 2 * r ^ 2 := by positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (N ω)),
      abs_of_nonneg hNonneg] using hSq
  have hJmajor : Integrable (fun ω => 2 * N ω ^ 2 + 2 * d ^ 2) P :=
    (hN2.const_mul 2).add (integrable_const _)
  refine Integrable.mono' hJmajor (hJ.aestronglyMeasurable.pow 2) ?_
  filter_upwards [hBound] with ω hw
  have hPos : 0 ≤ N ω + |d| := le_trans (abs_nonneg (J ω)) hw
  have hJ2 : J ω ^ 2 ≤ (N ω + |d|) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hw)
      (add_nonneg hPos (abs_nonneg (J ω))), sq_abs (J ω)]
  have hQuad : (N ω + |d|) ^ 2 ≤
      2 * (N ω) ^ 2 + 2 * d ^ 2 := by
    nlinarith [sq_nonneg (N ω - |d|), sq_abs d]
  have hNonneg : 0 ≤ 2 * N ω ^ 2 + 2 * d ^ 2 := by positivity
  simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (J ω)),
    abs_of_nonneg hNonneg] using le_trans hJ2 hQuad

-- Prove2me | solution 1 for AvramDividend.Classical.avram_oai_integrable_square_from_count_square_and_absolute_majorant_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:42:55.146803+00:00
-- url     : https://prove2.me/submissions/64d979df-b035-4ba5-8bc6-54862f5eb1a2

import Mathlib
open MeasureTheory
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (J N : Ω → ℝ) (c : ℝ)
    (hJ : Integrable J P)
    (hN2 : Integrable (fun ω => (N ω) ^ 2) P)
    (hNonneg : ∀ᵐ ω ∂P, 0 ≤ N ω)
    (hBound : ∀ᵐ ω ∂P, |J ω| ≤ N ω + |c|) :
    Integrable (fun ω => (J ω) ^ 2) P  := by
  have hMajor : Integrable (fun ω => 2 * (N ω) ^ 2 + 2 * c ^ 2) P :=
    (hN2.const_mul 2).add (integrable_const (2 * c ^ 2))
  apply hMajor.mono (hJ.aestronglyMeasurable.pow 2)
  filter_upwards [hNonneg, hBound] with ω hn hb
  have hDiff : 0 ≤ N ω + |c| - |J ω| := sub_nonneg.mpr hb
  have hSum : 0 ≤ N ω + |c| + |J ω| := by positivity
  have hProd := mul_nonneg hDiff hSum
  have hSq : (J ω) ^ 2 ≤ (N ω + |c|) ^ 2 := by
    nlinarith [sq_abs (J ω)]
  have hUpper : (J ω) ^ 2 ≤ 2 * (N ω) ^ 2 + 2 * c ^ 2 := by
    nlinarith [sq_nonneg (N ω - |c|), sq_abs c]
  change |(J ω) ^ 2| ≤ |2 * (N ω) ^ 2 + 2 * c ^ 2|
  rw [abs_of_nonneg (sq_nonneg (J ω)),
    abs_of_nonneg (show 0 ≤ 2 * (N ω) ^ 2 + 2 * c ^ 2 by positivity)]
  exact hUpper

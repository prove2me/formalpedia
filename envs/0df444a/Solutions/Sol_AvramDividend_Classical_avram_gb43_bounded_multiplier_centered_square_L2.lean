-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb43_bounded_multiplier_centered_square_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:36:33.03328+00:00
-- url     : https://prove2.me/submissions/56404be3-267b-4cea-a6e0-7503e3c3985e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical

/-- Multiplication by a bounded coefficient preserves a square moment. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (H R : Ω → ℝ) (B K : ℝ)
    (hH : Measurable H) (hR : Measurable R)
    (hK : 0 ≤ K) (hHb : ∀ ω, |H ω| ≤ K)
    (hR2 : Integrable (fun ω => (R ω) ^ 2) P)
    (hB : (∫ ω, (R ω) ^ 2 ∂P) ≤ B) :
    Integrable (fun ω => (H ω * R ω) ^ 2) P ∧
      (∫ ω, (H ω * R ω) ^ 2 ∂P) ≤ K ^ 2 * B := by
  have hmeas : Measurable (fun ω => (H ω * R ω) ^ 2) :=
    (hH.mul hR).pow_const 2
  have hmajor : Integrable (fun ω => K ^ 2 * (R ω) ^ 2) P :=
    hR2.const_mul (K ^ 2)
  have hpoint (ω : Ω) :
      (H ω * R ω) ^ 2 ≤ K ^ 2 * (R ω) ^ 2 := by
    have hh : (H ω) ^ 2 ≤ K ^ 2 := by
      nlinarith [sq_abs (H ω), abs_nonneg (H ω),
        sq_nonneg (K - |H ω|), hHb ω]
    calc
      _ = (H ω) ^ 2 * (R ω) ^ 2 := by ring
      _ ≤ K ^ 2 * (R ω) ^ 2 :=
        mul_le_mul_of_nonneg_right hh (sq_nonneg _)
  have hi : Integrable (fun ω => (H ω * R ω) ^ 2) P := by
    apply Integrable.mono' hmajor hmeas.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint ω
  refine ⟨hi, ?_⟩
  calc
    (∫ ω, (H ω * R ω) ^ 2 ∂P) ≤
        ∫ ω, K ^ 2 * (R ω) ^ 2 ∂P :=
      integral_mono hi hmajor hpoint
    _ = K ^ 2 * (∫ ω, (R ω) ^ 2 ∂P) := integral_const_mul _ _
    _ ≤ K ^ 2 * B :=
      mul_le_mul_of_nonneg_left hB (sq_nonneg _)

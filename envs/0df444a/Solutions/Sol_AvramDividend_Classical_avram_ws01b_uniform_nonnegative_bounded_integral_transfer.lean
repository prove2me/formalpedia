-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_uniform_nonnegative_bounded_integral_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T14:15:54.665654+00:00
-- url     : https://prove2.me/submissions/06c3dea0-25a5-4824-81c3-a42bb490e601

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Filter.Basic
import Theorems.Thm_AvramDividend_Classical_chat03_nonnegative_truncation_integral_tendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- Uniformly capped nonnegative integrable rewards transfer expectation across a.e. limits. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (R : ℝ)
    (hR : 0 ≤ R)
    (hInt : ∀ n, Integrable (Y n) P)
    (h0 : ∀ n ω, 0 ≤ Y n ω)
    (hCap : ∀ n ω, Y n ω ≤ R)
    (hConv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Z ω))) :
    Tendsto (fun n => ∫ ω, Y n ω ∂P)
      atTop (𝓝 (∫ ω, Z ω ∂P)) := by
  have hTrunc := chat03_nonnegative_truncation_integral_tendsto
    Y Z R hR
    (fun n => (hInt n).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall (h0 n))
    hConv
  have hLeft :
      (fun n => ∫ ω, min (Y n ω) R ∂P) =
        (fun n => ∫ ω, Y n ω ∂P) := by
    funext n
    apply integral_congr_ae
    filter_upwards [] with ω
    exact min_eq_left (hCap n ω)
  have hZcap : ∀ᵐ ω ∂P, Z ω ≤ R := by
    filter_upwards [hConv] with ω hω
    exact le_of_tendsto hω
      (Filter.Eventually.of_forall (fun n => hCap n ω))
  have hRight : (∫ ω, min (Z ω) R ∂P) = ∫ ω, Z ω ∂P := by
    apply integral_congr_ae
    filter_upwards [hZcap] with ω hω
    exact min_eq_left hω
  rw [hLeft, hRight] at hTrunc
  exact hTrunc

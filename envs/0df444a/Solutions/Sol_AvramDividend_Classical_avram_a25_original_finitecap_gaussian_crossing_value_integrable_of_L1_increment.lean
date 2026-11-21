-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_original_finitecap_gaussian_crossing_value_integrable_of_L1_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T10:01:17.46928+00:00
-- url     : https://prove2.me/submissions/1857e12a-1923-453d-8c4a-99eded50eede

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_finitecap_gaussian_cell_crossing_linear_envelope
open MeasureTheory Set AvramDividend.Classical
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    (w : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hw_cont : ContinuousOn w (Set.Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (Y R : Ω → ℝ) (hY : ∀ᵐ ω ∂P, 0 ≤ Y ω ∧ Y ω ≤ b)
    (hR : Integrable R P)
    (hV : AEStronglyMeasurable (fun ω =>
      if Y ω + R ω ≤ b then w (Y ω + R ω)
      else w b + (Y ω + R ω - b)) P) :
    Integrable (fun ω =>
      if Y ω + R ω ≤ b then w (Y ω + R ω)
      else w b + (Y ω + R ω - b)) P  := by
  obtain ⟨K, hK, hBound⟩ :=
    avram_a22_original_finitecap_gaussian_cell_crossing_linear_envelope
      w b hb hw_cont hw_neg
  let f : Ω → ℝ := fun ω =>
    if Y ω + R ω ≤ b then w (Y ω + R ω)
    else w b + (Y ω + R ω - b)
  have hGI : Integrable (fun ω => K + b + |R ω|) P := by
    exact (integrable_const (K + b)).add hR.abs
  have hDom : ∀ᵐ ω ∂P,
      ‖f ω‖ ≤ K + b + |R ω| := by
    filter_upwards [hY] with ω hy
    have hbR := hBound (Y ω) (R ω) hy.1 hy.2
    simpa only [Real.norm_eq_abs, f] using hbR
  exact Integrable.mono' hGI hV hDom

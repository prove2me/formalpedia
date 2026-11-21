-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_original_finitecap_gaussian_crossing_spatial_difference_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T10:01:25.616012+00:00
-- url     : https://prove2.me/submissions/cc199c99-0c29-4a0a-872a-09a72253159c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a25_original_finitecap_gaussian_crossing_value_difference_linear_envelope
open MeasureTheory Set AvramDividend.Classical
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    (w : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hw_cont : ContinuousOn w (Set.Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (Y R : Ω → ℝ) (hY : ∀ᵐ ω ∂P, 0 ≤ Y ω ∧ Y ω ≤ b)
    (hR : Integrable R P)
    (hMeas : AEStronglyMeasurable (fun ω =>
      (if Y ω + R ω ≤ b then w (Y ω + R ω)
       else w b + (Y ω + R ω - b)) - w (Y ω)) P) :
    Integrable (fun ω =>
      (if Y ω + R ω ≤ b then w (Y ω + R ω)
       else w b + (Y ω + R ω - b)) - w (Y ω)) P  := by
  obtain ⟨K, hK, hBound⟩ :=
    avram_a25_original_finitecap_gaussian_crossing_value_difference_linear_envelope
      w b hb hw_cont hw_neg
  have hEnv : Integrable (fun ω => K + b + |R ω|) P :=
    (integrable_const (K + b)).add hR.abs
  have hDom : ∀ᵐ ω ∂P,
      ‖(if Y ω + R ω ≤ b then w (Y ω + R ω)
        else w b + (Y ω + R ω - b)) - w (Y ω)‖
        ≤ K + b + |R ω| := by
    filter_upwards [hY] with ω hy
    have hV := hBound (Y ω) (R ω) hy.1 hy.2
    simpa only [Real.norm_eq_abs] using hV
  exact Integrable.mono' hEnv hMeas hDom

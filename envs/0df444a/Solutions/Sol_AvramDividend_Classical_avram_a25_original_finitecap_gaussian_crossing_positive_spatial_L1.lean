-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_original_finitecap_gaussian_crossing_positive_spatial_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T10:01:33.848617+00:00
-- url     : https://prove2.me/submissions/3b36585f-08e6-4823-8b19-2f61bfdb776b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a25_original_finitecap_gaussian_crossing_spatial_difference_L1
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
      max ((if Y ω + R ω ≤ b then w (Y ω + R ω)
       else w b + (Y ω + R ω - b)) - w (Y ω)) 0) P  := by
  let f : Ω → ℝ := fun ω =>
    (if Y ω + R ω ≤ b then w (Y ω + R ω)
      else w b + (Y ω + R ω - b)) - w (Y ω)
  have hFI : Integrable f P :=
    avram_a25_original_finitecap_gaussian_crossing_spatial_difference_L1
      w b hb hw_cont hw_neg Y R hY hR hMeas
  have hHalf : Integrable (fun ω => (f ω + |f ω|) / 2) P :=
    (hFI.add hFI.abs).div_const 2
  have hp (z : ℝ) : max z 0 = (z + |z|) / 2 := by
    by_cases hz : 0 ≤ z
    · rw [max_eq_left hz, abs_of_nonneg hz]
      ring
    · have hz' : z ≤ 0 := le_of_not_ge hz
      rw [max_eq_right hz', abs_of_nonpos hz']
      ring
  convert hHalf using 1
  funext ω
  exact hp (f ω)

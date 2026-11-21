-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_complete_negative_mark_cutoff_future_count_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T10:21:43.960739+00:00
-- url     : https://prove2.me/submissions/7d44cad3-ef31-43f3-829a-5d8165995848

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_physical_L2_auto
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original finite negative-cutoff future physical marked increment
is integrable automatically from the exact original count L2 theorem. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (cut : ℕ) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℝ :=
      ((T : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    Integrable (fun ω => (N ω).toReal - r) P := by
  intro N r
  have hL2 :
      MemLp (fun ω => (N ω).toReal - r) 2 P := by
    simpa only [N, r, one_mul] using
      (avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_physical_L2_auto
        X s T cut (fun _ => (1 : ℝ))
        stronglyMeasurable_const (1 : ℝ) (by simp))
  exact hL2.integrable (by norm_num)

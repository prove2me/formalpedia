-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva87_original_zero_clock_total_compensated_marked_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:43:52.246938+00:00
-- url     : https://prove2.me/submissions/d6f7895d-3977-4ac5-a647-1c8cffdd0d28

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva83_original_zero_clock_negative_mark_compensator_integral
import Theorems.Thm_AvramDividend_Classical_avram_bva86_original_marked_zero_clock_supported_jump_integral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hMeas : Measurable (fun u : ℝ≥0 =>
      (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hSupport : ∀ p : ℝ≥0 × ℝ, H ((p.1, ω), p.2) ≠ 0 → p.1 = 0) :
    (∫ p, H ((p.1, ω), p.2)
      ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) -
    (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict (Icc 0 (0 : ℝ))).map Real.toNNReal)) = 0 := by
  have hJump :=
    avram_bva86_original_marked_zero_clock_supported_jump_integral
      X ω hMeas H hSupport
  have hComp :=
    avram_bva83_original_zero_clock_negative_mark_compensator_integral X H ω
  rw [hJump, hComp]
  ring

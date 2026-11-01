-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_negative_count_nonzero_iff_residual_strict_ae_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:16:05.005991+00:00
-- url     : https://prove2.me/submissions/84ddb8fc-01dd-440d-a6ed-dfae73845da6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_negative_rectangle_zero_iff_no_source_jump
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_drift_residual_strict_interval_iff_jump

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- On one P-full event, actual negative source-count occupancy matches
strict original BV drift-residual growth on every interval in a horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iio (0 : ℝ)) ≠ 0 ↔
      (s : ℝ) * X.drift - X.X s ω <
        (t : ℝ) * X.drift - X.X t ω) := by
  filter_upwards
    [avram_wave4_04a_bv_actual_drift_residual_strict_interval_iff_jump
      X hBV hFinite T hT] with ω hω
  intro s t hst htT
  have hJump := hω s t hst htT
  have hZero :=
    avram_wave4_04a_actual_intrinsic_negative_rectangle_zero_iff_no_source_jump
      X ω s t
  constructor
  · intro hCount
    apply hJump.mpr
    by_contra hNoJump
    apply hCount
    apply hZero.mpr
    intro v hv
    by_contra hvJump
    exact hNoJump ⟨v, hv, hvJump⟩
  · intro hStrict hCountZero
    obtain ⟨v, hv, hvJump⟩ := hJump.mp hStrict
    exact hvJump (hZero.mp hCountZero v hv)

-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_drift_residual_strict_interval_iff_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:59:32.55512+00:00
-- url     : https://prove2.me/submissions/cb952b3d-20e9-443d-afb4-07f2419318de

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_source_nonzero_jump_iff_strict_drift_residual_jump

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- On the genuine BV source path, a strict drift-residual increment on a
time interval occurs if and only if the interval contains a genuine X jump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      ((s : ℝ) * X.drift - X.X s ω <
          (t : ℝ) * X.drift - X.X t ω ↔
        ∃ u : ℝ≥0, u ∈ Ioc s t ∧
          X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) := by
  classical
  filter_upwards
    [avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
        X hBV hFinite T hT,
      bv_actual_levy_residual_ae_monotone_all_times X hBV]
    with ω hNoJumpInterval hmono
  intro s t hst htT
  let Y : ℝ≥0 → ℝ := fun u => (u : ℝ) * X.drift - X.X u ω
  have hm : Monotone Y := hmono
  change (Y s < Y t ↔
    ∃ u : ℝ≥0, u ∈ Ioc s t ∧
      X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
  constructor
  · intro hStrict
    by_contra hno
    have hNoJump : ∀ u : ℝ≥0, u ∈ Ioc s t →
        X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 := by
      intro u hu
      by_contra hne
      exact hno ⟨u, hu, hne⟩
    have hEq : Y t = Y s :=
      hNoJumpInterval s t hst htT hNoJump
    exact (ne_of_lt hStrict) hEq.symm
  · rintro ⟨u, ⟨hsu, hut⟩, huJump⟩
    have huPos : 0 < u := lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ s) hsu
    have hStrictJump : Function.leftLim Y u < Y u := by
      exact
        (avram_wave4_04a_actual_source_nonzero_jump_iff_strict_drift_residual_jump
          X ω u huPos).mpr huJump
    have hLeftBound : Y s ≤ Function.leftLim Y u :=
      hm.le_leftLim hsu
    have hRightBound : Y u ≤ Y t := hm hut
    exact lt_of_lt_of_le (lt_of_le_of_lt hLeftBound hStrictJump) hRightBound

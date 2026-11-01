-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_nojump_event_ae_eq_drift_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:13:27.179235+00:00
-- url     : https://prove2.me/submissions/4d42bd23-6651-4f4e-b80b-fc824fc11fa2

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
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

/-- Genuine source jump avoidance agrees P-almost surely with a drift-only
original Lévy increment on the exact same sample and filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t) :
    {ω : Ω | ∀ u : ℝ≥0, u ∈ Ioc s t →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0} =ᵐ[P]
      {ω : Ω | X.X t ω - X.X s ω =
        ((t : ℝ) - (s : ℝ)) * X.drift} := by
  classical
  have hT : 0 < t + 1 := by positivity
  have htT : t ≤ t + 1 :=
    le_add_of_nonneg_right (by positivity : (0 : ℝ≥0) ≤ 1)
  filter_upwards
    [avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
        X hBV hFinite (t + 1) hT,
      bv_actual_levy_residual_ae_monotone_all_times X hBV]
    with ω hNoJumpInterval hmono
  let Y : ℝ≥0 → ℝ := fun u => (u : ℝ) * X.drift - X.X u ω
  have hm : Monotone Y := hmono
  apply propext
  change (∀ u : ℝ≥0, u ∈ Ioc s t →
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) ↔
    X.X t ω - X.X s ω = ((t : ℝ) - (s : ℝ)) * X.drift
  constructor
  · intro hNoJump
    have heq : Y t = Y s :=
      hNoJumpInterval s t hst htT hNoJump
    dsimp [Y] at heq
    nlinarith
  · intro hDelta u hu
    have heq : Y t = Y s := by
      dsimp [Y]
      nlinarith
    by_contra hNonzero
    have huPos : 0 < u :=
      lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ s) hu.1
    have hStrictJump : Function.leftLim Y u < Y u :=
      (avram_wave4_04a_actual_source_nonzero_jump_iff_strict_drift_residual_jump
        X ω u huPos).mpr hNonzero
    have hleft : Y s ≤ Function.leftLim Y u := hm.le_leftLim hu.1
    have hright : Y u ≤ Y t := hm hu.2
    have hStrict : Y s < Y t :=
      lt_of_lt_of_le (lt_of_le_of_lt hleft hStrictJump) hright
    exact (ne_of_lt hStrict) heq.symm

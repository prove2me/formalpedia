-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_bv_stopped_min_away_zero_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:07:40.44191+00:00
-- url     : https://prove2.me/submissions/8597add9-68cb-4e4b-a1ac-86247866e2db

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_bv_strict_lower_exit_undershoot_ae_ws01c
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_up_first_iff_finite_stopped_min

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Genuine BV stopped two-sided reserve avoids the q-scale jump at zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    ∀ᵐ ω ∂P,
      min (twoSidedExitUpTime X (a - x) ω)
        (twoSidedExitDownTime X (-x) ω) < ⊤ →
      x + X.X (min (twoSidedExitUpTime X (a - x) ω)
        (twoSidedExitDownTime X (-x) ω)).toNNReal ω ≠ 0 := by
  have hUnder := bv_strict_lower_exit_undershoot_ae_ws01c
    X hX q hq W hW hBV a x ha hx0 hxa
  filter_upwards [hUnder] with ω hUnderω
  intro hfin
  let U : ℝ≥0∞ := twoSidedExitUpTime X (a - x) ω
  let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
  have hM : min U D < ⊤ := hfin
  change x + X.X (min U D).toNNReal ω ≠ 0
  rcases lt_trichotomy U D with hUp | hEq | hDown
  · have hfinite : U ≠ ⊤ := ne_of_lt (lt_of_lt_of_le hUp le_top)
    have hu : (U.toNNReal : ℝ≥0∞) =
        (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) := by
      simpa only [U, twoSidedExitUpTime] using
        (ENNReal.coe_toNNReal hfinite)
    have hhit : X.X U.toNNReal ω = a - x :=
      firstUpcrossing_value_eq_threshold X (a - x)
        (sub_nonneg.mpr hxa) ω U.toNNReal hu
    rw [min_eq_left hUp.le, hhit]
    have hval : x + (a - x) = a := by ring
    rw [hval]
    exact ne_of_gt ha
  · have hfinite : U < ⊤ := by
      simpa only [min_eq_left hEq.le] using hM
    have hContr : U < D :=
      (avram_root29_03_up_first_iff_finite_stopped_min
        X a x ha ω).2 ⟨min_eq_left hEq.le, hfinite⟩
    exact False.elim ((not_lt_of_ge hEq.ge) hContr)
  · have hUnder' : x + X.X D.toNNReal ω < 0 := hUnderω hDown
    rw [min_eq_right hDown.le]
    exact ne_of_lt hUnder'

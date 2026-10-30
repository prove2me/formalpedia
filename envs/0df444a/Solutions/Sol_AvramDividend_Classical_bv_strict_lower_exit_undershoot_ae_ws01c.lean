-- Prove2me | solution 1 for AvramDividend.Classical.bv_strict_lower_exit_undershoot_ae_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:13:43.253052+00:00
-- url     : https://prove2.me/submissions/603e73db-7055-47d1-a748-e98d7408ee70

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_strict_lower_exit_no_creeping_ae
import Theorems.Thm_AvramDividend_Classical_chat04_firstDowncrossing_value_le_threshold

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-! The original BV strict lower exit has a genuine negative undershoot a.e. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    ∀ᵐ ω ∂P,
      twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω →
      x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω < 0 := by
  have hNoCreep :
      ∀ᵐ ω ∂P,
        twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω →
        x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω ≠ 0 := by
    simpa only [twoSidedExitDownTime, twoSidedExitUpTime] using
      (bv_strict_lower_exit_no_creeping_ae
        X hX q hq W hW hBV a x ha hx0 hxa)
  filter_upwards [hNoCreep] with ω hnc
  intro hLower
  let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
  let U : ℝ≥0∞ := twoSidedExitUpTime X (a - x) ω
  have hDU : D < U := hLower
  have hfinite : D ≠ ⊤ := ne_of_lt (lt_of_lt_of_le hDU le_top)
  have hd : (D.toNNReal : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) := by
    simpa only [D, twoSidedExitDownTime] using
      (ENNReal.coe_toNNReal hfinite)
  have hdown : X.X D.toNNReal ω ≤ -x :=
    chat04_firstDowncrossing_value_le_threshold X (-x) ω D.toNNReal hd
  have hnonpos : x + X.X D.toNNReal ω ≤ 0 := by linarith
  have hnonzero : x + X.X D.toNNReal ω ≠ 0 := hnc hLower
  change x + X.X D.toNNReal ω < 0
  rcases lt_or_eq_of_le hnonpos with hlt | heq
  · exact hlt
  · exact False.elim (hnonzero heq)

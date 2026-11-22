-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_strict_lower_exit_undershoot_ae_no_standing_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T08:43:42.247162+00:00
-- url     : https://prove2.me/submissions/c6bcde4a-345a-4330-b8cf-e92d10ce1864

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_strict_lower_exit_no_creeping_ae_no_standing_public
import Theorems.Thm_AvramDividend_Classical_chat04_firstDowncrossing_value_le_threshold

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
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
      (p2m81_bv_strict_lower_exit_no_creeping_ae_no_standing_public
        X q φ hq hφ hroot W hW hBV a x ha hx0 hxa)
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

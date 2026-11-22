-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_strict_lower_exit_no_creeping_of_cap_slopes_no_standing_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T08:37:28.963802+00:00
-- url     : https://prove2.me/submissions/5381a766-046f-47c1-81e8-5e18725e3968

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_actual_raw_clock_positive_germ_of_cap_slopes_no_standing_public
import Theorems.Thm_AvramDividend_Classical_bv_positive_shifted_increment_contact_right_interval_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_strict_lower_exit_no_creeping_of_contact_right_germ_ws01b

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (δ : ℕ → ℝ≥0)
    (hδpos : ∀ n, 0 < δ n)
    (hRatio : ∀ n, (δ n : ℝ) ≤ 2 * (δ (n + 1) : ℝ))
    (hCover : ∀ (N : ℕ) (t : ℝ≥0), 0 < t → t < δ N →
      ∃ n : ℕ, N ≤ n ∧ δ (n + 1) ≤ t ∧ t ≤ δ n)
    (hCapSlope : ∀ N : ℕ, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        (X.drift * (δ n : ℝ) -
          (X.X (((twoSidedExitDownTime X (-x) ω) ⊓
              (N : ℝ≥0∞)).toNNReal + δ n) ω -
            X.X (((twoSidedExitDownTime X (-x) ω) ⊓
              (N : ℝ≥0∞)).toNNReal) ω)) /
          (δ n : ℝ))
        atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂P,
      twoSidedExitDownTime X (-x) ω <
        twoSidedExitUpTime X (a - x) ω →
      x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω ≠ 0 := by
  apply bv_strict_lower_exit_no_creeping_of_contact_right_germ_ws01b X a x
  filter_upwards [p2m81_bv_actual_raw_clock_positive_germ_of_cap_slopes_no_standing_public X q φ hq hφ hroot hBV
    (twoSidedExitDownTime X (-x)) δ hδpos hRatio hCover hCapSlope] with ω hω hlt hzero
  have hfin : twoSidedExitDownTime X (-x) ω < ⊤ := lt_of_lt_of_le hlt le_top
  refine ⟨(twoSidedExitDownTime X (-x) ω).toNNReal, ENNReal.coe_toNNReal hfin.ne, ?_⟩
  exact bv_positive_shifted_increment_contact_right_interval_ws01c (fun s => X.X s ω) _ (-x)
    (by linarith) (hω hfin)

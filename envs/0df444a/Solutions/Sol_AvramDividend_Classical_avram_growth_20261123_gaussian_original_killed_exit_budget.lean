-- Prove2me | solution 1 for AvramDividend.Classical.avram_growth_20261123_gaussian_original_killed_exit_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T08:17:32.909103+00:00
-- url     : https://prove2.me/submissions/0d059e76-f86e-43eb-9ada-c480564ad0d8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_hjb_finite_original_upcross_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_hjb_finite_clock_budget_to_full
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_topcap_w_nonnegative_everywhere
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_eq_corrected
import Theorems.Thm_AvramDividend_Classical_avram_growth_20261123_original_corrected_exit_clocks_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section


theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hTop : C = ⊤) (hw0 : 0 ≤ w 0)
    (hwcont : ContinuousOn w (Ici 0)) (hwneg : ∀ y < 0, w y = 0)
    (hwsmooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwgen : ∀ y, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwgrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hSigma : X.σ ≠ 0) :
    ∀ b : ℝ, 1 ≤ b →
      w b * (twoSidedExitExpectation X q b 1).toReal ≤ w 1 := by
  intro b hb
  let up : Ω → ℝ≥0∞ := twoSidedExitUpTimeCorrected X (b - 1)
  let down : Ω → ℝ≥0∞ := twoSidedExitDownTimeCorrected X (-1)
  let v : Ω → ℝ≥0∞ := fun omega =>
    ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (up omega))))
  obtain ⟨hu, hd⟩ := avram_growth_20261123_original_corrected_exit_clocks_measurable X b
  have huMeas : Measurable up := hu
  have hdMeas : Measurable down := hd
  have hvMeas : Measurable v := by
    dsimp [v]
    fun_prop
  have hw1 : 0 ≤ w 1 :=
    avram_ubv_top9_original_topcap_w_nonnegative_everywhere
      w C hTop hw0 hwcont hwneg hwsmooth hwgrad 1
  have hwb : 0 ≤ w b :=
    avram_ubv_top9_original_topcap_w_nonnegative_everywhere
      w C hTop hw0 hwcont hwneg hwsmooth hwgrad b
  have hFinite (k : Nat) :
      w b * (∫⁻ omega, if up omega < down omega ∧
        up omega ≤ (k : ℝ≥0∞) then v omega else 0 ∂P).toReal ≤ w 1 := by
    simpa [up, down, v] using
      avram_p4_f6_hjb_finite_original_upcross_budget
        X hX hBV hν hSigma q hq w C hC hw0 hwcont hwneg
        hwsmooth hwgen hwgrad hTop b k hb
  have hFull :=
    avram_p4_f6_hjb_finite_clock_budget_to_full
      P up down v huMeas hdMeas hvMeas (w b) (w 1) hwb hw1 hFinite
  simpa [twoSidedExitExpectationCorrected, up, down, v,
    chat04_twoSidedExitExpectation_eq_corrected] using hFull

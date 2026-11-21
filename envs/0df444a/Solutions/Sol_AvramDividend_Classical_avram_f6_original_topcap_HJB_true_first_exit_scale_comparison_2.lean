-- Prove2me | solution 2 for AvramDividend.Classical.avram_f6_original_topcap_HJB_true_first_exit_scale_comparison
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T15:07:51.550618+00:00
-- url     : https://prove2.me/submissions/6e4745ae-d2b0-4a5c-abef-585737d30d9c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_UBV_true_positive_discount_qscale_exists
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_topcap_true_killed_first_exit_expected_HJB_budget
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_topcap_w_nonnegative_everywhere
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_UBV_expected_killed_HJB_budget_implies_scale_dom
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
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
    (hwgrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    ∃ W : ℝ → ℝ, IsScaleFunction X q W ∧
      ∃ A : ℝ, 0 ≤ A ∧ ∀ y : ℝ, 1 ≤ y → w y ≤ A * W y := by
  classical
  obtain ⟨W, hW⟩ :=
    avram_f6_original_UBV_true_positive_discount_qscale_exists X hX hBV q hq
  have hw1 : 0 ≤ w 1 :=
    avram_ubv_top9_original_topcap_w_nonnegative_everywhere
      w C hTop hw0 hwcont hwneg hwsmooth hwgrad 1
  have hExit :=
    avram_f6_original_topcap_true_killed_first_exit_expected_HJB_budget
      X hX hBV hν q hq w C hC hTop hw0 hwcont hwneg hwsmooth hwgen hwgrad
  obtain ⟨A, hA, hComp⟩ :=
    avram_f6_original_UBV_expected_killed_HJB_budget_implies_scale_dom
      X hX hBV q hq w W hw1 hW hExit
  exact ⟨W, hW, A, hA, hComp⟩

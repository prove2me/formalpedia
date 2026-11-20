-- Prove2me | solution 2 for AvramDividend.Classical.avram_f6_original_topcap_nonzero_nu_HJB_exponential_growth_only
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T21:06:50.921878+00:00
-- url     : https://prove2.me/submissions/aa068401-28b4-4e84-801f-fcf2485815ca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_topcap_HJB_true_first_exit_scale_comparison
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_UBV_HJB_scale_compare_implies_exponential_growth
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
    ∃ (θ K : ℝ), 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, 0 ≤ y → w y ≤ K * Real.exp (θ * y)  := by
  obtain ⟨W, hW, A, hA, hComp⟩ :=
    avram_f6_original_topcap_HJB_true_first_exit_scale_comparison
      X hX hBV hν q hq w C hC hTop hw0 hwcont hwneg hwsmooth hwgen hwgrad
  exact avram_f6_original_UBV_HJB_scale_compare_implies_exponential_growth
    X hBV q hq w hw0 hwcont W hW A hA hComp

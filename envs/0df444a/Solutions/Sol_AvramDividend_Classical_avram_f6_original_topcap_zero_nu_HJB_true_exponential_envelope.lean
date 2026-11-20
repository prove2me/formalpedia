-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_topcap_zero_nu_HJB_true_exponential_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:40:46.251271+00:00
-- url     : https://prove2.me/submissions/70fd6d70-35be-4124-be46-d6ec48a29db2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn16_gaussian_HJB_global_exponential_growth
import Theorems.Thm_AvramDividend_Classical_avram_gbB36_interior_cap_positive_value_from_gradient
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hTop : C = ⊤) (hw0 : 0 ≤ w 0)
    (hwcont : ContinuousOn w (Ici 0)) (hwneg : ∀ y < 0, w y = 0)
    (hwsmooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwgen : ∀ y, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwgrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      (∀ y : ℝ, 0 ≤ y → 0 ≤ w y) ∧
      (∀ y : ℝ, 0 ≤ y → w y ≤ K * Real.exp (θ * y)) := by
  obtain ⟨θ, K, hθ, hK, hbound⟩ :=
    avram_p4_f4_turn16_gaussian_HJB_global_exponential_growth
      X hX hBV hν q hq w C hC hw0 hwcont hwneg
      hwsmooth hwgen hwgrad hTop
  refine ⟨θ, K, hθ, hK, ?_, ?_⟩
  · intro y hy
    apply avram_gbB36_interior_cap_positive_value_from_gradient
      C w hw0 hwcont hwsmooth hwgrad y hy
    simp [hTop]
  · intro y hy
    exact hbound y

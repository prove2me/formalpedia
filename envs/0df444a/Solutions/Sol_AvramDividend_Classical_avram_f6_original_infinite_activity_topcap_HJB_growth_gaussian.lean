-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_infinite_activity_topcap_HJB_growth_gaussian
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T21:51:33.575182+00:00
-- url     : https://prove2.me/submissions/c97e11ed-23a8-405c-a6e6-6f33e8c683a4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_topcap_nonzero_nu_HJB_exp_subroot_gaussian
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
    (hInfinite : X.ν (Iio (0 : ℝ)) = ⊤)
    (hCase : 0 < X.σ) :
    ∃ (θ K : ℝ), 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, 0 ≤ y → w y ≤ K * Real.exp (θ * y)  := by
  obtain ⟨θ, K, p, lam, hθ, hK, hp, hlam, hsep, hroot, hBound⟩ :=
    avram_f6_original_topcap_nonzero_nu_HJB_exp_subroot_gaussian
    X hX hBV hν q hq w C hC hTop hw0 hwcont hwneg
    hwsmooth hwgen hwgrad hCase
  exact ⟨θ, K, hθ, hK, hBound⟩

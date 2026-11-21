-- Prove2me | solution 3 for AvramDividend.Classical.avram_f6_original_topcap_nonzero_nu_HJB_exponential_subroot_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T15:05:40.535353+00:00
-- url     : https://prove2.me/submissions/ea022cc6-f185-43a4-acb1-feae6af88144
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_topcap_nonzero_nu_HJB_exponential_growth_only
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_UBV_psi_root_above_theta_all
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
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
    ∃ (θ K p lam : ℝ), 0 ≤ θ ∧ 0 ≤ K ∧ 0 < p ∧ 0 < lam ∧ θ < lam ∧
      X.ψ lam = p ∧
      ∀ y : ℝ, 0 ≤ y → w y ≤ K * Real.exp (θ * y) := by
  classical
  obtain ⟨θ, K, hθ, hK, hwGrowth⟩ :=
    avram_f6_original_topcap_nonzero_nu_HJB_exponential_growth_only
      X hX hBV hν q hq w C hC hTop hw0 hwcont hwneg
      hwsmooth hwgen hwgrad
  obtain ⟨p, lam, hp, hlam, hθlam, hroot⟩ :=
    avram_f6_original_UBV_psi_root_above_theta_all X hBV θ
  exact ⟨θ, K, p, lam, hθ, hK, hp, hlam, hθlam, hroot, hwGrowth⟩

-- Prove2me | solution 2 for AvramDividend.Classical.avram_f6_original_topcap_nonzero_nu_HJB_exp_subroot_gaussian
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:20:52.817623+00:00
-- url     : https://prove2.me/submissions/463c6c41-2157-4b0c-9d96-db94ea29b4a2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_positive_gaussian_qscale_exists
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_original_killed_HJB_scale_comparison
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_topcap_w_nonnegative_everywhere
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_UBV_HJB_scale_compare_implies_exponential_growth
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_UBV_psi_root_above_theta_all
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
    (hSigma : 0 < X.σ) :
    ∃ (θ K p lam : ℝ), 0 ≤ θ ∧ 0 ≤ K ∧ 0 < p ∧ 0 < lam ∧ θ < lam ∧
      X.ψ lam = p ∧
      ∀ y : ℝ, 0 ≤ y → w y ≤ K * Real.exp (θ * y)  := by
  obtain ⟨W, hW, hWone⟩ :=
    avram_p4_f6_positive_gaussian_qscale_exists X hX q hq hSigma
  have hwone : 0 ≤ w 1 :=
    avram_ubv_top9_original_topcap_w_nonnegative_everywhere
      w C hTop hw0 hwcont hwneg hwsmooth hwgrad 1
  let A : ℝ := w 1 / W 1
  have hA : 0 ≤ A := div_nonneg hwone (le_of_lt hWone)
  have hdom : ∀ y : ℝ, 1 ≤ y → w y ≤ A * W y := by
    intro y hy
    have hscale :=
      avram_p4_f6_original_killed_HJB_scale_comparison
        X hX hBV hν (ne_of_gt hSigma) q hq w C hC hw0 hwcont
        hwneg hwsmooth hwgen hwgrad hTop W hW hWone y hy
    change w y ≤ (w 1 / W 1) * W y
    calc
      w y ≤ w 1 * W y / W 1 := (le_div_iff₀ hWone).mpr hscale
      _ = (w 1 / W 1) * W y := by ring
  obtain ⟨θ, K, hθ, hK, hgrowth⟩ :=
    avram_f6_original_UBV_HJB_scale_compare_implies_exponential_growth
      X hBV q hq w hw0 hwcont W hW A hA hdom
  obtain ⟨p, lam, hp, hlam, hlt, hroot⟩ :=
    avram_f6_original_UBV_psi_root_above_theta_all X hBV θ
  exact ⟨θ, K, p, lam, hθ, hK, hp, hlam, hlt, hroot, hgrowth⟩

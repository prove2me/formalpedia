-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f5_topcap_analytic_HJB_global_exponential_growth
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:25:25.372737+00:00
-- url     : https://prove2.me/submissions/17b6be69-e042-4a29-bf2d-aa35cba21236
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_positive_gaussian_qscale_exists
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_original_killed_HJB_scale_comparison
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_gaussian_scale_exponential_upper_envelope
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_scale_dominated_growth_bridge
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hTop : C = ⊤) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, w y ≤ K * Real.exp (θ * y) := by
  have hσpos : 0 < X.σ := lt_of_le_of_ne X.σ_nonneg (Ne.symm hσ)
  obtain ⟨W, hW, hWone⟩ :=
    avram_p4_f6_positive_gaussian_qscale_exists X hX q hq hσpos
  obtain ⟨θ, K, hθ, hK, hWexp⟩ :=
    avram_p4_f6_gaussian_scale_exponential_upper_envelope X hσpos q W hW
  have hmono : Monotone W := scaleFunction_monotone X q W hW
  have hcontIcc : ContinuousOn w (Icc (0 : ℝ) 1) := by
    apply hw_cont.mono
    intro y hy
    exact hy.1
  have hcompact : IsCompact (w '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn hcontIcc
  obtain ⟨u, hu⟩ : BddAbove (w '' Icc (0 : ℝ) 1) := hcompact.bddAbove
  let M : ℝ := max 0 u
  have hM : 0 ≤ M := le_max_left _ _
  have hunit : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → w y ≤ M := by
    intro y hy0 hy1
    have hwle : w y ≤ u := hu (Set.mem_image_of_mem _ ⟨hy0, hy1⟩)
    exact hwle.trans (le_max_right _ _)
  let A : ℝ := max 0 (w 1 / W 1)
  have hA : 0 ≤ A := le_max_left _ _
  have hdom : ∀ b : ℝ, 1 ≤ b → w b ≤ A * W b := by
    intro b hb
    have hcomp : w b * W 1 ≤ w 1 * W b :=
      avram_p4_f6_original_killed_HJB_scale_comparison
        X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
        hw_smooth hw_gen hw_grad hTop W hW hWone b hb
    have hratio : w b ≤ (w 1 * W b) / W 1 :=
      (le_div_iff₀ hWone).mpr hcomp
    have hWb : 0 ≤ W b := le_trans (le_of_lt hWone) (hmono hb)
    calc
      w b ≤ (w 1 * W b) / W 1 := hratio
      _ = (w 1 / W 1) * W b := by ring
      _ ≤ A * W b := mul_le_mul_of_nonneg_right (le_max_right _ _) hWb
  refine ⟨θ, max M (A * K), hθ, ?_, ?_⟩
  · exact le_trans hM (le_max_left _ _)
  · exact avram_p4_f6_scale_dominated_growth_bridge
      w W θ A K M hθ hA hK hM hw_neg hunit hdom hWexp

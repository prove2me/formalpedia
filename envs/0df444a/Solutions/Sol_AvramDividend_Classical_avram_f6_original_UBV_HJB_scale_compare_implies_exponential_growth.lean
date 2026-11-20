-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_UBV_HJB_scale_compare_implies_exponential_growth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T21:06:26.896734+00:00
-- url     : https://prove2.me/submissions/5ff0cc0a-e305-4dc8-a26b-bf07447cf42f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_UBV_qScale_true_global_exponential_upper
import Theorems.Thm_AvramDividend_Classical_avram_f6_scale_comparator_local_bound_to_global_exponential
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0) (hwcont : ContinuousOn w (Ici 0))
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (A : ℝ) (hA : 0 ≤ A)
    (hComp : ∀ y : ℝ, 1 ≤ y → w y ≤ A * W y) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, 0 ≤ y → w y ≤ K * Real.exp (θ * y) := by
  obtain ⟨θ, K1, hθ, hK1, hWUpper⟩ :=
    avram_f6_original_UBV_qScale_true_global_exponential_upper
      X hBV q hq W hW
  have hsub : Icc (0 : ℝ) 1 ⊆ Ici 0 := fun _ h => h.1
  have hCompact : IsCompact (w '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn (hwcont.mono hsub)
  obtain ⟨K0, hUpper⟩ := hCompact.bddAbove
  have hK0 : 0 ≤ K0 := by
    have h0 : w 0 ≤ K0 :=
      hUpper ⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩
    linarith
  have hLocal : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → w y ≤ K0 := by
    intro y hy hy1
    exact hUpper ⟨y, ⟨hy, hy1⟩, rfl⟩
  obtain ⟨K, hK, hGrowth⟩ :=
    avram_f6_scale_comparator_local_bound_to_global_exponential
      w W θ A K0 K1 hθ hA hK0 hK1 hLocal hWUpper hComp
  exact ⟨θ, K, hθ, hK, hGrowth⟩

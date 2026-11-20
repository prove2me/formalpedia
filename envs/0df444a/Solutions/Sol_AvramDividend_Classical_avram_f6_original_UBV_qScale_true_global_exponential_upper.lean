-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_UBV_qScale_true_global_exponential_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T21:03:34.272855+00:00
-- url     : https://prove2.me/submissions/5ecbd171-ab92-480a-b03e-bf5ff4e7c8cb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_global_weighted_norm_bddAbove
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, W y ≤ K * Real.exp (θ * y) := by
  have hqone : 0 < q + 1 := by linarith
  obtain ⟨θ, hθ, hroot⟩ :=
    positive_esscher_root_of_unbounded_variation X hBV (q + 1) hqone
  have hψ : q < X.ψ θ := by rw [hroot]; linarith
  obtain ⟨K, hK⟩ :=
    scaleFunction_global_weighted_norm_bddAbove X q W hW θ hθ.le hψ
  have hKpos : 0 ≤ K :=
    le_trans (norm_nonneg _) (hK ⟨0, rfl⟩)
  refine ⟨θ, K, hθ.le, hKpos, ?_⟩
  intro y
  have hb : ‖Real.exp (-(θ * y)) * W y‖ ≤ K :=
    hK ⟨y, rfl⟩
  have hval : Real.exp (-(θ * y)) * W y ≤ K :=
    le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hb)
  calc
    W y = Real.exp (θ * y) * (Real.exp (-(θ * y)) * W y) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp (θ * y) * K :=
      mul_le_mul_of_nonneg_left hval (Real.exp_pos _).le
    _ = K * Real.exp (θ * y) := mul_comm _ _

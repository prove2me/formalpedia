-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f6_gaussian_scale_exponential_upper_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:18:49.250133+00:00
-- url     : https://prove2.me/submissions/1c6cf4e9-bb8a-4144-a7c0-fb28db02be37

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_psi_superlinear_of_positive_sigma
import Theorems.Thm_AvramDividend_Classical_scaleFunction_global_weighted_norm_bddAbove
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : 0 < X.σ)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, W y ≤ K * Real.exp (θ * y) := by
  obtain ⟨θ, hθ1, hψgrowth⟩ :=
    AvramDividend.Classical.gaussian_psi_superlinear_of_positive_sigma X hσ
      (max q 0 + 1)
  have hθ0 : 0 ≤ θ := by linarith
  have hθpos : 0 < θ := by linarith
  have hqψ : q < X.ψ θ := by
    have hlarge : (max q 0 + 1) * θ < X.ψ θ :=
      (lt_div_iff₀ hθpos).mp (hψgrowth θ le_rfl)
    have hzero : (0 : ℝ) ≤ max q 0 := le_max_right q 0
    have hq : q ≤ max q 0 := le_max_left q 0
    have hmul : 0 ≤ (max q 0 + 1) * (θ - 1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  obtain ⟨K, hK⟩ :=
    (AvramDividend.Classical.scaleFunction_global_weighted_norm_bddAbove
      X q W hW θ hθ0 hqψ)
  have hK0 : 0 ≤ K :=
    le_trans (norm_nonneg (Real.exp (-(θ * (0 : ℝ))) * W 0))
      (hK ⟨0, rfl⟩)
  refine ⟨θ, K, hθ0, hK0, ?_⟩
  intro y
  have hbound : ‖Real.exp (-(θ * y)) * W y‖ ≤ K :=
    hK ⟨y, rfl⟩
  have hexpPos : 0 < Real.exp (-(θ * y)) := Real.exp_pos _
  have hnorm : Real.exp (-(θ * y)) * |W y| ≤ K := by
    simpa [Real.norm_eq_abs, abs_mul, abs_of_pos hexpPos] using hbound
  have hexp : Real.exp (θ * y) * Real.exp (-(θ * y)) = 1 := by
    rw [← Real.exp_add]
    simp
  have habs : |W y| ≤ K * Real.exp (θ * y) := by
    calc
      |W y| = (Real.exp (θ * y) * Real.exp (-(θ * y))) * |W y| := by rw [hexp, one_mul]
      _ = Real.exp (θ * y) * (Real.exp (-(θ * y)) * |W y|) := by ring
      _ ≤ Real.exp (θ * y) * K := mul_le_mul_of_nonneg_left hnorm (le_of_lt (Real.exp_pos _))
      _ = K * Real.exp (θ * y) := mul_comm _ _
  exact (le_abs_self (W y)).trans habs

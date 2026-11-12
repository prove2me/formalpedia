-- Prove2me | solution 2 for AvramDividend.Classical.avram_anoise22_original_gaussian_cutoff_exact_second_moment
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T23:49:39.353405+00:00
-- url     : https://prove2.me/submissions/1a600f63-1fbd-4a8b-9ae7-2f620fb8869b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_cutoff_gaussian_measurable_square_moment_certificate
import Theorems.Thm_AvramDividend_Classical_avram_ja19_integrable_square_add_of_L2_components
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original physical cutoff second moment from independent Gaussian/jump L2 components. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      Integrable (fun ω =>
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ^ 2) P ∧
      (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ^ 2 ∂P) =
        (t : ℝ) * X.σ ^ 2 +
          (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν) := by
  intro n t
  obtain ⟨G, J, hEq, hGmeas, hJmeas, hGsq, hJsq, hCross, hGmom, hJmom⟩ :=
    avram_ja21_original_cutoff_gaussian_measurable_square_moment_certificate
      X hX hFinite n t
  have hSumSq : Integrable (fun ω => (G ω + J ω) ^ 2) P :=
    avram_ja19_integrable_square_add_of_L2_components
      G J hGmeas hJmeas hGsq hJsq
  have hGJ : Integrable (fun ω => G ω * J ω) P := by
    have hProdExpr : (fun ω => G ω * J ω) =
        (fun ω => (1 / 2 : ℝ) *
          ((G ω + J ω) ^ 2 - ((G ω) ^ 2 + (J ω) ^ 2))) := by
      funext ω
      ring
    rw [hProdExpr]
    exact (hSumSq.sub (hGsq.add hJsq)).const_mul (1 / 2 : ℝ)
  have hOriginalSq : Integrable (fun ω =>
      (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ^ 2) P := by
    apply hSumSq.congr
    filter_upwards [hEq] with ω hω
    simp only [hω]
  have hMom : (∫ ω, (G ω + J ω) ^ 2 ∂P) =
      (t : ℝ) * X.σ ^ 2 +
        (t : ℝ) *
          (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν) := by
    have hfun : (fun ω => (G ω + J ω) ^ 2) =
        (fun ω => (G ω) ^ 2 + (J ω) ^ 2 + 2 * (G ω * J ω)) := by
      funext ω
      ring
    rw [hfun]
    have hOuter :
        (∫ ω, (G ω) ^ 2 + (J ω) ^ 2 + 2 * (G ω * J ω) ∂P) =
        (∫ ω, (G ω) ^ 2 + (J ω) ^ 2 ∂P) +
        (∫ ω, 2 * (G ω * J ω) ∂P) := by
      exact integral_add (hGsq.add hJsq) (hGJ.const_mul 2)
    have hInner :
        (∫ ω, (G ω) ^ 2 + (J ω) ^ 2 ∂P) =
        (∫ ω, (G ω) ^ 2 ∂P) + (∫ ω, (J ω) ^ 2 ∂P) := by
      exact integral_add hGsq hJsq
    calc
      (∫ ω, (G ω) ^ 2 + (J ω) ^ 2 + 2 * (G ω * J ω) ∂P) =
          (∫ ω, (G ω) ^ 2 + (J ω) ^ 2 ∂P) +
          (∫ ω, 2 * (G ω * J ω) ∂P) := hOuter
      _ = (∫ ω, (G ω) ^ 2 ∂P) +
          (∫ ω, (J ω) ^ 2 ∂P) +
          2 * (∫ ω, G ω * J ω ∂P) := by
            rw [hInner, integral_const_mul]
      _ = _ := by
            rw [hGmom, hJmom, hCross]
            ring
  refine ⟨hOriginalSq, ?_⟩
  calc
    (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ^ 2 ∂P) =
        (∫ ω, (G ω + J ω) ^ 2 ∂P) := by
          apply integral_congr_ae
          filter_upwards [hEq] with ω hω
          rw [hω]
    _ = _ := hMom

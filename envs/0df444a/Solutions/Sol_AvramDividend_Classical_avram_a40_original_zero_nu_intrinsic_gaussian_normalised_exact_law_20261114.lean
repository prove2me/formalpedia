-- Prove2me | solution 1 for AvramDividend.Classical.avram_a40_original_zero_nu_intrinsic_gaussian_normalised_exact_law_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:11:58.270414+00:00
-- url     : https://prove2.me/submissions/b9609947-5086-4db1-a953-b26ba1ac608a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_zero_nu_intrinsic_gaussian_limit_sameX_companion
import Theorems.Thm_AvramDividend_Classical_avram_gbB264_original_zerojump_normalised_increment_exact_gaussian_law
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hNu : X.ν = 0) (hPositive : 0 < X.σ)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∀ t : ℝ≥0,
      Measure.map (fun ω => R t ω / X.σ) P = gaussianReal 0 t := by
  obtain ⟨Y, hYnu, hYσ, hEq⟩ :=
    avram_a22_original_zero_nu_intrinsic_gaussian_limit_sameX_companion
      X hNu R hR
  have hPosY : 0 < Y.σ := by rw [hYσ]; exact hPositive
  intro t
  have hLaw :=
    avram_gbB264_original_zerojump_normalised_increment_exact_gaussian_law
      Y hYnu hPosY 0 t (show (0 : ℝ≥0) ≤ t from zero_le)
  have hMapEq : (fun ω => R t ω / X.σ) =ᵐ[P]
      (fun ω => ((Y.X t ω - Y.X 0 ω) -
        (((t - 0 : ℝ≥0) : ℝ) * Y.c)) / Y.σ) := by
    filter_upwards [hEq] with ω hω
    rw [hω t, Y.X_zero ω, hYσ]
    simp
  calc
    Measure.map (fun ω => R t ω / X.σ) P =
      Measure.map (fun ω => ((Y.X t ω - Y.X 0 ω) -
        (((t - 0 : ℝ≥0) : ℝ) * Y.c)) / Y.σ) P :=
          Measure.map_congr hMapEq
    _ = gaussianReal 0 (t - 0) := hLaw
    _ = gaussianReal 0 t := by simp

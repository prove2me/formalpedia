-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_limit_gaussian_zero_time_square_moment_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:22:24.825708+00:00
-- url     : https://prove2.me/submissions/8e6ca8cb-0e1e-40e6-8999-14c0e9714cdc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin18_original_intrinsic_gaussian_residual_zero_time_public
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The physical intrinsic residual limit has zero initial square moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω))) :
    Integrable (fun ω => (R 0 ω) ^ 2) P ∧
      (∫ ω, (R 0 ω) ^ 2 ∂P) = 0 := by
  have hZero : ∀ᵐ ω ∂P, R 0 ω = 0 :=
    avram_mix_fin18_original_intrinsic_gaussian_residual_zero_time_public
      X R hR
  have hSq : (fun ω => (R 0 ω) ^ 2) =ᵐ[P]
      (fun _ : Ω => (0 : ℝ)) := by
    filter_upwards [hZero] with ω hω
    simp [hω]
  have hInt : Integrable (fun ω => (R 0 ω) ^ 2) P :=
    (integrable_zero Ω ℝ P).congr hSq.symm
  have hMoment : (∫ ω, (R 0 ω) ^ 2 ∂P) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hZero] with ω hω
    simp [hω]
  exact ⟨hInt, hMoment⟩

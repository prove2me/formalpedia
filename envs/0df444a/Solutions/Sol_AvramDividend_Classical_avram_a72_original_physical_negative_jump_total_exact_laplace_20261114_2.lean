-- Prove2me | solution 2 for AvramDividend.Classical.avram_a72_original_physical_negative_jump_total_exact_laplace_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:40:23.817925+00:00
-- url     : https://prove2.me/submissions/759849d3-14fe-46d0-b2b1-cd45b2e21233
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a76_finite_negative_activity_levy_gaussian_jump_exponent_split_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a77_original_finite_activity_physical_negative_jump_compound_poisson_laplace_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hPositive : 0 < X.σ) (hNu : X.ν ≠ 0)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (t : ℝ≥0) (ht : 0 < t) (θ : ℝ) (hθ : 0 < θ)
    (H J : Ω → ℝ)
    (hHMeas : Measurable H) (hJMeas : Measurable J)
    (hHEq : H =ᵐ[P] R t)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0)
    (hDecomp : ∀ ω, H ω + J ω =
      X.X t ω -
        (t : ℝ) * (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) :
    (∫ ω, Real.exp (θ * J ω) ∂P) =
      Real.exp ((t : ℝ) * X.ψ θ -
        θ * ((t : ℝ) * (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) -
        (t : ℝ) * (X.σ ^ 2 * θ ^ 2 / 2)) := by
  have hCompound :=
    avram_a77_original_finite_activity_physical_negative_jump_compound_poisson_laplace_20261114
      X hFinite t θ (le_of_lt hθ) J hJMeas hJEq
  have hSplit :=
    avram_a76_finite_negative_activity_levy_gaussian_jump_exponent_split_20261114
      X hFinite θ (le_of_lt hθ)
  rw [hCompound, hSplit]
  congr 1
  ring

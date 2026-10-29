-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bf_new_gaussian_interior_generator_of_weighted_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T01:03:43.170974+00:00
-- url     : https://prove2.me/submissions/75b93f65-f402-4be2-b778-6467a149c067

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_of_gaussian
import Theorems.Thm_AvramDividend_Classical_gaussian_psi_superlinear_of_positive_sigma
import Theorems.Thm_AvramDividend_Classical_scaleFunction_origin_zero_of_superlinear_psi_nonnegative_q
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_Ioi_of_zero_origin_C2
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_nonzero_at_finite_cstar_of_tilted_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_q_harmonic_of_nonzero_factor_gaussian
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal
/-- Gaussian interior generator q-harmonicity from the exact residual Laplace family. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) (ha : 0 < (cstar W).toReal)
    (hweighted : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable W x ∧
        X.generator W x - q * W x = 0 := by
  have hC2 : ContDiffOn ℝ 2 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_two_of_gaussian X hX q hq W hW hσ
  have hzero : W 0 = 0 :=
    scaleFunction_origin_zero_of_superlinear_psi_nonnegative_q
      X q (le_of_lt hq) W hW
      (gaussian_psi_superlinear_of_positive_sigma X hσ)
  have hcont : ContinuousOn
      (fun x : ℝ => X.generator W x - q * W x) (Ioi 0) :=
    generator_residual_continuousOn_Ioi_of_zero_origin_C2
      X q W hW hzero hC2
  obtain ⟨hWpos, φ, hφ, hmono⟩ :=
    scaleFunction_tilted_positive_monotone X hX q hq W hW
  have hWdiff : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ W y := by
    intro y hy
    exact (hC2.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hy)
  have hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0 :=
    scaleDeriv_nonzero_at_finite_cstar_of_tilted_monotone
      X hX q hq W hW ha hWpos hWdiff ⟨φ, hφ, hmono⟩
  have hc : (0 : ENNReal) < cstar W :=
    (ENNReal.toReal_pos_iff.1 ha).1
  exact scaleFunction_generator_q_harmonic_of_nonzero_factor_gaussian
    X hX q hq W hW hσ hc hC2 hk hcont hweighted

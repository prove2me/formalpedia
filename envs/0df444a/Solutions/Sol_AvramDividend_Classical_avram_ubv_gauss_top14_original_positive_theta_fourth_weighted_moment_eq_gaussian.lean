-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss_top14_original_positive_theta_fourth_weighted_moment_eq_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:29:08.606424+00:00
-- url     : https://prove2.me/submissions/66c56790-1b27-4fdb-94af-185eb42f75dd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_normalised_mgf_matches_gaussian_real
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_normalised_exponential_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual zero-jump centred Levy increment has the Gaussian fourth
    exponential moment at each positive transform parameter. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 < θ) :
    (∫ ω, ((X.X t ω - (t : ℝ) * X.c) / X.σ) ^ 4 *
       Real.exp (θ * ((X.X t ω - (t : ℝ) * X.c) / X.σ)) ∂P) =
    (∫ z : ℝ, z ^ 4 * Real.exp (θ * z) ∂(gaussianReal 0 t)) := by
  let Z : Ω → ℝ := fun ω => (X.X t ω - (t : ℝ) * X.c) / X.σ
  have hIoi : Ioi (0 : ℝ) ⊆ integrableExpSet Z P := by
    intro u hu
    exact avram_p4_a_gaussian_zero_jump_original_normalised_exponential_integrable
      X X hν rfl hσ t u (le_of_lt hu)
  have hInt : θ ∈ interior (integrableExpSet Z P) :=
    mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (isOpen_Ioi.mem_nhds hθ) hIoi)
  have hGaussianInt : θ ∈ interior
      (integrableExpSet id (gaussianReal 0 t)) := by
    simp [integrableExpSet_id_gaussianReal]
  have hMgf : EqOn (mgf Z P) (mgf id (gaussianReal 0 t)) (Ioi (0 : ℝ)) := by
    intro u hu
    exact avram_p4_a_gaussian_original_normalised_mgf_matches_gaussian_real
      X X hν rfl hσ t u (le_of_lt hu)
  have hFourth := hMgf.iteratedDeriv_of_isOpen isOpen_Ioi 4
  change (∫ ω, Z ω ^ 4 * Real.exp (θ * Z ω) ∂P) =
    (∫ z : ℝ, z ^ 4 * Real.exp (θ * z) ∂(gaussianReal 0 t))
  calc
    (∫ ω, Z ω ^ 4 * Real.exp (θ * Z ω) ∂P) =
      iteratedDeriv 4 (mgf Z P) θ := (iteratedDeriv_mgf hInt 4).symm
    _ = iteratedDeriv 4 (mgf id (gaussianReal 0 t)) θ := hFourth hθ
    _ = (∫ z : ℝ, z ^ 4 * Real.exp (θ * z) ∂(gaussianReal 0 t)) :=
      iteratedDeriv_mgf hGaussianInt 4

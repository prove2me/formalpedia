-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_localise_original_gaussian_fourth_moment_positive_fatou
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T11:02:04.847789+00:00
-- url     : https://prove2.me/submissions/5e3d7cc7-c6a9-4829-8237-9b5beb3fded4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss_top14_original_positive_theta_fourth_weighted_moment_eq_gaussian
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_normalised_exponential_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ) (t : ℝ≥0)
    (hMeas : Measurable (fun ω : Ω => (X.X t ω - (t : ℝ) * X.c) / X.σ)) :
    (∫⁻ ω, ENNReal.ofReal (((X.X t ω - (t : ℝ) * X.c) / X.σ) ^ 4) ∂P) ≤
    Filter.liminf (fun n : ℕ => ENNReal.ofReal
      (∫ z : ℝ, z ^ 4 * Real.exp ((1 / ((n : ℝ) + 1)) * z) ∂(gaussianReal 0 t))) atTop := by
  let Z : Ω → ℝ := fun ω => (X.X t ω - (t : ℝ) * X.c) / X.σ
  let θ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let F : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (Z ω ^ 4 * Real.exp (θ n * Z ω))
  have hθpos (n : ℕ) : 0 < θ n := by dsimp [θ]; positivity
  have hθlim : Tendsto θ atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hIoi : Ioi (0 : ℝ) ⊆ integrableExpSet Z P := by
    intro u hu
    exact avram_p4_a_gaussian_zero_jump_original_normalised_exponential_integrable X X hν rfl hσ t u (le_of_lt hu)
  have hInt (n : ℕ) : θ n ∈ interior (integrableExpSet Z P) :=
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (isOpen_Ioi.mem_nhds (hθpos n)) hIoi)
  have hFI (n : ℕ) : Integrable (fun ω => Z ω ^ 4 * Real.exp (θ n * Z ω)) P :=
    integrable_pow_mul_exp_of_mem_interior_integrableExpSet (hInt n) 4
  have hFMeas (n : ℕ) : Measurable (F n) := by
    have hZ : Measurable Z := hMeas
    have hMul : Measurable (fun ω => Z ω ^ 4 * Real.exp (θ n * Z ω)) := (hZ.pow_const 4).mul (Real.measurable_exp.comp (measurable_const.mul hZ))
    exact ENNReal.measurable_ofReal.comp hMul
  have hFlim : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (ENNReal.ofReal (Z ω ^ 4))) := by
    filter_upwards [] with ω
    have hθω : Tendsto (fun n => θ n * Z ω) atTop (𝓝 (0 : ℝ)) := by
      simpa using hθlim.mul_const (Z ω)
    have hExp : Tendsto (fun n => Real.exp (θ n * Z ω)) atTop (𝓝 (1 : ℝ)) := by
      have hExp' := (Real.continuous_exp.tendsto 0).comp hθω
      change Tendsto (fun n => Real.exp (θ n * Z ω)) atTop (𝓝 (Real.exp (0 : ℝ))) at hExp'
      simpa only [Real.exp_zero] using hExp'
    have hPow : Tendsto (fun _ : ℕ => Z ω ^ 4) atTop (𝓝 (Z ω ^ 4)) := tendsto_const_nhds
    have hProd := hPow.mul hExp
    have h := (ENNReal.continuous_ofReal.tendsto (Z ω ^ 4)).comp
      (show Tendsto (fun n => Z ω ^ 4 * Real.exp (θ n * Z ω))
          atTop (𝓝 (Z ω ^ 4)) by simpa only [mul_one] using hProd)
    exact h
  have hFatou : (∫⁻ ω, ENNReal.ofReal (Z ω ^ 4) ∂P) ≤ Filter.liminf (fun n => ∫⁻ ω, F n ω ∂P) atTop := by
    have hEq : (fun ω => ENNReal.ofReal (Z ω ^ 4)) =ᵐ[P] (fun ω => Filter.liminf (fun n => F n ω) atTop) := by
      filter_upwards [hFlim] with ω hω
      exact hω.liminf_eq.symm
    calc
      (∫⁻ ω, ENNReal.ofReal (Z ω ^ 4) ∂P) =
          (∫⁻ ω, Filter.liminf (fun n => F n ω) atTop ∂P) :=
        lintegral_congr_ae hEq
      _ ≤ Filter.liminf (fun n => ∫⁻ ω, F n ω ∂P) atTop :=
        lintegral_liminf_le (μ := P) (u := atTop) (f := F) hFMeas
  have hIntegral (n : ℕ) : (∫⁻ ω, F n ω ∂P) = ENNReal.ofReal (∫ z : ℝ, z ^ 4 * Real.exp (θ n * z) ∂(gaussianReal 0 t)) := by
    have hNonneg : 0 ≤ᵐ[P] (fun ω => Z ω ^ 4 * Real.exp (θ n * Z ω)) :=
      Filter.Eventually.of_forall (fun ω =>
        mul_nonneg (by positivity) (le_of_lt (Real.exp_pos _)))
    have hConv := ofReal_integral_eq_lintegral_ofReal (hFI n) hNonneg
    calc
      (∫⁻ ω, F n ω ∂P) =
          ENNReal.ofReal (∫ ω, Z ω ^ 4 * Real.exp (θ n * Z ω) ∂P) := hConv.symm
      _ = ENNReal.ofReal (∫ z : ℝ, z ^ 4 * Real.exp (θ n * z)
            ∂(gaussianReal 0 t)) := by
        congr 1
        exact avram_ubv_gauss_top14_original_positive_theta_fourth_weighted_moment_eq_gaussian X hν hσ t (θ n) (hθpos n)
  change (∫⁻ ω, ENNReal.ofReal (Z ω ^ 4) ∂P) ≤
    Filter.liminf (fun n => ENNReal.ofReal
      (∫ z : ℝ, z ^ 4 * Real.exp (θ n * z) ∂(gaussianReal 0 t))) atTop
  calc
    (∫⁻ ω, ENNReal.ofReal (Z ω ^ 4) ∂P) ≤
      Filter.liminf (fun n => ∫⁻ ω, F n ω ∂P) atTop := hFatou
    _ = Filter.liminf (fun n => ENNReal.ofReal
      (∫ z : ℝ, z ^ 4 * Real.exp (θ n * z) ∂(gaussianReal 0 t))) atTop := by
        congr 1
        funext n
        exact hIntegral n

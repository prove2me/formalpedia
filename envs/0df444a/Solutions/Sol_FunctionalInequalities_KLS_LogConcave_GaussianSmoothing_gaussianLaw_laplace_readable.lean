-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_laplace_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:35:49.839001+00:00
-- url     : https://prove2.me/submissions/1d2bbbdd-2d2b-4710-9316-55112a9206d2

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments

section
open MeasureTheory ProbabilityTheory Filter Topology
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] in
/-- The Gaussian noise law `γ_s` is the tilt of Lebesgue measure by `e^{-s‖y‖²}`. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_eq_tilted {s : ℝ} (hs : 0 < s) :
    gaussianLaw (V := E) s = (volume : Measure E).tilted (fun y => -s * ‖y‖ ^ 2) := by
  have hmass : (∫ y : E, Real.exp (-s * ‖y‖ ^ 2)) = mass (V := E) s := integral_kernel hs
  unfold gaussianLaw Measure.tilted normalizedKernel kernel
  rw [hmass]
omit [CompleteSpace E] in
private theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.ofReal_integral_exp_gaussian {s : ℝ} (hs : 0 < s) (z : E) :
    ((∫ y : E, Real.exp (-s * ‖y‖ ^ 2 + ⟪z, y⟫) : ℝ) : ℂ) =
      (Real.pi / (s : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ) *
        Complex.exp (‖z‖ ^ 2 / (4 * (s : ℂ))) := by
  have hb : 0 < (s : ℂ).re := by simpa using hs
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := E) hb 1 z
  calc
    ((∫ y : E, Real.exp (-s * ‖y‖ ^ 2 + ⟪z, y⟫) : ℝ) : ℂ) =
        ∫ y : E, (Real.exp (-s * ‖y‖ ^ 2 + ⟪z, y⟫) : ℂ) := integral_complex_ofReal.symm
    _ = ∫ y : E, Complex.exp (-(s : ℂ) * ‖y‖ ^ 2 + 1 * ⟪z, y⟫) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [Complex.ofReal_exp]
      push_cast
      ring_nf
    _ = _ := by rw [h]; simp
omit [CompleteSpace E] in
/-- Laplace transform of `γ_s`: `∫ e^{⟪z,y⟫} dγ_s = e^{‖z‖²/(4s)}` (variance `ε = 1/(2s)`). -/
theorem solution {s : ℝ} (hs : 0 < s) (z : E) :
    (∫ y, Real.exp ⟪z, y⟫ ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw (V := E) s)) = Real.exp (‖z‖ ^ 2 / (4 * s)) := by
  rw [FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_eq_tilted hs, integral_tilted]
  simp only [smul_eq_mul]
  have hnum : (∫ y : E, Real.exp (-s * ‖y‖ ^ 2) /
      (∫ w : E, Real.exp (-s * ‖w‖ ^ 2)) * Real.exp ⟪z, y⟫) =
      (∫ y : E, Real.exp (-s * ‖y‖ ^ 2 + ⟪z, y⟫)) /
        (∫ w : E, Real.exp (-s * ‖w‖ ^ 2)) := by
    rw [← integral_div]
    congr 1
    funext y
    rw [Real.exp_add]
    ring
  rw [hnum]
  have h0 := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.ofReal_integral_exp_gaussian hs (0 : E)
  simp only [inner_zero_left, add_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    Complex.ofReal_zero, zero_div, Complex.exp_zero, mul_one] at h0
  have hz := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.ofReal_integral_exp_gaussian hs z
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hpC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hne : (Real.pi / (s : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => (div_ne_zero hpC hsC) h.1
  apply Complex.ofReal_injective
  rw [Complex.ofReal_div, hz, h0, Complex.ofReal_exp]
  push_cast
  field_simp

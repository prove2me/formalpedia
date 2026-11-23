-- Prove2me | solution 1 for DedekindZeta.GammaIntegral.gammaComplex_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:26:09.861029+00:00
-- url     : https://prove2.me/submissions/61503897-83b3-4f3b-add1-e90716925a5d

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta DedekindZeta.GammaIntegral
open Classical
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.GammaIntegral
theorem _root_.solution {s : ℂ} (hs : 0 < s.re) :
    gammaComplex s = DedekindZeta.LComplex s := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  -- Polar/cpow bookkeeping lemma: `x · (x²)^{s-1} = x^{2s-1}` for `x > 0`.
  have hkey : ∀ x : ℝ, 0 < x →
      (x : ℂ) * ((x ^ 2 : ℝ) : ℂ) ^ (s - 1) = (x : ℂ) ^ (2 * s - 1) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    rw [show ((x ^ 2 : ℝ) : ℂ) = (x : ℂ) * (x : ℂ) by push_cast; ring,
        Complex.mul_cpow_ofReal_nonneg hx.le hx.le, ← Complex.cpow_add _ _ hx0]
    nth_rewrite 1 [← Complex.cpow_one (x : ℂ)]
    rw [← Complex.cpow_add _ _ hx0]; congr 1; ring
  -- `x⁻¹ · x^{2s} = x^{2s-1}` for `x > 0`.
  have hkey2 : ∀ x : ℝ, 0 < x →
      ((x⁻¹ : ℝ) : ℂ) * (x : ℂ) ^ (2 * s) = (x : ℂ) ^ (2 * s - 1) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    rw [Complex.ofReal_inv, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hx0]
    congr 1; ring
  -- `(1/(2π))^s = (2π)^{-s}`.
  have hpow : (1 / (2 * (Real.pi : ℂ))) ^ s = (2 * (Real.pi : ℂ)) ^ (-s) := by
    have harg : (2 * (Real.pi : ℂ)).arg ≠ Real.pi := by
      rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
          Complex.arg_ofReal_of_nonneg (by positivity)]
      exact Real.pi_pos.ne
    rw [one_div, Complex.inv_cpow _ _ harg, Complex.cpow_neg]
  -- The radial Mellin integral (substitution `u = x²` then `Complex.Gamma`).
  have hrad : (∫ x in Set.Ioi (0 : ℝ),
        (x : ℂ) ^ (2 * s - 1) * ((Real.exp (-2 * Real.pi * x ^ 2) : ℝ) : ℂ))
      = (1 / 2) * ((1 / ((2 * Real.pi : ℝ) : ℂ)) ^ s * Complex.Gamma s) := by
    have h2 := Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := s) (r := 2 * Real.pi) hs
      (by positivity)
    have h3 := integral_comp_rpow_Ioi
      (fun u : ℝ => (u : ℂ) ^ (s - 1) * Complex.exp (-(((2 * Real.pi : ℝ) : ℂ) * (u : ℂ))))
      (p := 2) two_ne_zero
    rw [h2] at h3
    rw [← h3, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx' : (0 : ℝ) < x := hx
    rw [show ((2 : ℝ) - 1) = (1 : ℝ) by norm_num, Real.rpow_one, Real.rpow_two,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), Complex.real_smul]
    rw [← hkey x hx']
    rw [show ((Real.exp (-2 * Real.pi * x ^ 2) : ℝ) : ℂ)
          = Complex.exp (-(((2 * Real.pi : ℝ) : ℂ) * ((x ^ 2 : ℝ) : ℂ))) by
        rw [Complex.ofReal_exp]; congr 1; push_cast; ring]
    push_cast; ring
  -- The angular integral contributes `2π`.
  have hang : (∫ _ in Set.Ioo (-Real.pi) Real.pi, (1 : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by
    rw [setIntegral_const, Real.volume_real_Ioo,
      max_eq_left (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi - -Real.pi),
      Complex.real_smul, mul_one]
    push_cast; ring
  -- Measurability/finiteness of the multiplicative-Haar density.
  have hd : Measurable (fun z : ℂ => ENNReal.ofReal (2 / Real.pi * (‖z‖ ^ 2)⁻¹)) :=
    (((continuous_norm.pow 2).measurable.inv).const_mul (2 / Real.pi)).ennreal_ofReal
  -- Unfold and pass to a plain Lebesgue integral, then to polar coordinates.
  unfold gammaComplex
  rw [integral_withDensity_eq_integral_toReal_smul₀ hd.aemeasurable
      (ae_of_all _ fun z => ENNReal.ofReal_lt_top)]
  have hfun : (fun z : ℂ => (ENNReal.ofReal (2 / Real.pi * (‖z‖ ^ 2)⁻¹)).toReal •
        ((Real.exp (-2 * Real.pi * ‖z‖ ^ 2) : ℝ) * (‖z‖ : ℂ) ^ (2 * s)))
      = fun z : ℂ => ((2 / Real.pi * (‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) *
        (((Real.exp (-2 * Real.pi * ‖z‖ ^ 2) : ℝ) : ℂ) * (‖z‖ : ℂ) ^ (2 * s)) := by
    funext z
    rw [ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
  rw [hfun, ← Complex.integral_comp_polarCoord_symm,
    show _root_.polarCoord.target
      = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi from rfl]
  simp only [Complex.norm_polarCoord_symm]
  -- Rewrite the integrand on the polar target as a pure radial function.
  trans (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
      2 / (Real.pi : ℂ) * ((p.1 : ℂ) ^ (2 * s - 1) *
        ((Real.exp (-2 * Real.pi * p.1 ^ 2) : ℝ) : ℂ)))
  · refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) (fun p hp => ?_)
    have h1 : (0 : ℝ) < p.1 := hp.1
    rw [abs_of_pos h1, Complex.real_smul]
    have hco : (p.1 : ℂ) * ((2 / Real.pi * (p.1 ^ 2)⁻¹ : ℝ) : ℂ)
        = (2 / (Real.pi : ℂ)) * ((p.1⁻¹ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul,
        show p.1 * (2 / Real.pi * (p.1 ^ 2)⁻¹) = 2 / Real.pi * p.1⁻¹ by
          field_simp]
      push_cast; ring
    rw [← mul_assoc, hco, mul_assoc,
      show ((p.1⁻¹ : ℝ) : ℂ) * (((Real.exp (-2 * Real.pi * p.1 ^ 2) : ℝ) : ℂ)
            * (p.1 : ℂ) ^ (2 * s))
          = ((Real.exp (-2 * Real.pi * p.1 ^ 2) : ℝ) : ℂ)
            * (((p.1⁻¹ : ℝ) : ℂ) * (p.1 : ℂ) ^ (2 * s)) by ring,
      hkey2 p.1 h1]
    ring
  -- Fubini: factor into radial × angular.
  trans ((∫ x in Set.Ioi (0 : ℝ),
      2 / (Real.pi : ℂ) * ((x : ℂ) ^ (2 * s - 1) *
        ((Real.exp (-2 * Real.pi * x ^ 2) : ℝ) : ℂ)))
      * (∫ _ in Set.Ioo (-Real.pi) Real.pi, (1 : ℂ)))
  · rw [← setIntegral_prod_mul, Measure.volume_eq_prod]; simp_rw [mul_one]
  rw [hang, integral_const_mul, hrad, DedekindZeta.LComplex,
    show ((2 * Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) by push_cast; ring, hpow]
  field_simp
end DedekindZeta.GammaIntegral

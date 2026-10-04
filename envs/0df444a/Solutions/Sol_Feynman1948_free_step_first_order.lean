-- Prove2me | solution 1 for Feynman1948.free_step_first_order
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T22:04:52.803959+00:00
-- url     : https://prove2.me/submissions/5a04204a-6ce2-4fac-b97a-3542beeb303f

import Definitions.Def_Feynman1948_WaveEquation
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.RealDeriv


open Complex MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace

private lemma gaussian_fourier (b : ℂ) (hb : 0 < b.re) (w : ℝ) :
    𝓕 (fun x : ℝ => Complex.exp (-b * x ^ 2)) w =
      (Real.pi / b) ^ (1 / 2 : ℂ) * Complex.exp (-(2 * Real.pi * (w : ℂ)) ^ 2 / (4 * b)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  have he (x : ℝ) : ((-2 * Real.pi * x * w : ℝ) : ℂ) * I =
      I * (-2 * Real.pi * (w : ℂ)) * x := by push_cast; ring
  simp_rw [he]
  rw [fourierIntegral_gaussian hb]
  congr 3
  ring

/-- Gaussian regularization paired against a Schwartz function. This is a direct
Fourier duality identity for strictly positive real damping; it does not yet
assert the boundary value at imaginary damping. -/
theorem gaussian_schwartz_pairing (b : ℂ) (hb : 0 < b.re) (ψ : SchwartzMap ℝ ℂ) :
    ∫ x : ℝ, Complex.exp (-b * x ^ 2) * ψ x =
      ∫ w : ℝ, ((Real.pi / b) ^ (1 / 2 : ℂ) *
        Complex.exp (-(2 * Real.pi * (w : ℂ)) ^ 2 / (4 * b))) * (𝓕 ψ) w := by
  let g : ℝ → ℂ := fun x => Complex.exp (-b * x ^ 2)
  have hg : Integrable g := by
    simpa [g] using integrable_cexp_quadratic hb 0 0
  have hi := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := volume) (ν := volume) (e := Real.fourierChar) (L := -(innerₗ ℝ)) continuous_fourierChar
    (by fun_prop) hg (𝓕 ψ).integrable
  have hflip : (-(innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ)).flip = -(innerₗ ℝ) := by
    ext
    rfl
  rw [hflip] at hi
  have he (w : ℝ) : 𝓕⁻ g w = (Real.pi / b) ^ (1 / 2 : ℂ) *
      Complex.exp (-(2 * Real.pi * (w : ℂ)) ^ 2 / (4 * b)) := by
    rw [Real.fourierInv_eq_fourier_neg, gaussian_fourier b hb]
    congr 3
    push_cast
    ring
  change (∫ w : ℝ, 𝓕⁻ g w * (𝓕 ψ) w) =
    ∫ x : ℝ, g x * 𝓕⁻ ((𝓕 ψ : SchwartzMap ℝ ℂ) : ℝ → ℂ) x at hi
  simp_rw [he] at hi
  rw [← SchwartzMap.fourierInv_coe, FourierTransform.fourierInv_fourier_eq] at hi
  exact hi.symm


open Complex Filter MeasureTheory Set Topology

/-- The Gaussian regularization converges to the ordinary oscillatory integral
when the amplitude is integrable. This does not use a conditionally convergent
Fresnel integral or exchange two undamped integrations. -/
theorem oscillatory_gaussian_abel_limit (c : ℝ) (ψ : ℝ → ℂ) (hψ : Integrable ψ) :
    Tendsto (fun δ : ℝ => ∫ x : ℝ,
      Complex.exp (-((δ : ℂ) - I * c) * (x : ℂ) ^ 2) * ψ x)
      (nhdsWithin 0 (Ioi 0))
      (𝓝 (∫ x : ℝ, Complex.exp (I * c * (x : ℂ) ^ 2) * ψ x)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖ψ x‖)
  · apply Filter.Eventually.of_forall
    intro δ
    exact (by fun_prop : Continuous (fun x : ℝ =>
      Complex.exp (-((δ : ℂ) - I * c) * (x : ℂ) ^ 2))).aestronglyMeasurable.mul
        hψ.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    apply Filter.Eventually.of_forall
    intro x
    rw [norm_mul, norm_cexp_neg_mul_sq]
    have hre : ((δ : ℂ) - I * c).re = δ := by simp
    rw [hre]
    calc
      Real.exp (-δ * x ^ 2) * ‖ψ x‖ ≤ 1 * ‖ψ x‖ :=
        mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (le_of_lt hδ)) (sq_nonneg x)))
          (norm_nonneg _)
      _ = ‖ψ x‖ := one_mul _
  · exact hψ.norm
  · apply Filter.Eventually.of_forall
    intro x
    have hc : Continuous (fun δ : ℝ =>
      Complex.exp (-((δ : ℂ) - I * c) * (x : ℂ) ^ 2) * ψ x) := by fun_prop
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds


open Complex Filter MeasureTheory Set Topology

/-- Boundary convergence on the frequency side, with an integrable amplitude. -/
theorem gaussian_frequency_abel_limit (c : ℝ) (hc : 0 < c)
    (f : ℝ → ℂ) (hf : Integrable f) :
    Tendsto (fun δ : ℝ => ∫ w : ℝ,
      Complex.exp (-((2 * Real.pi * w : ℝ) : ℂ) ^ 2 / (4 * ((δ : ℂ) - I * c))) * f w)
      (nhdsWithin 0 (Ioi 0))
      (𝓝 (∫ w : ℝ, Complex.exp (-((2 * Real.pi * w : ℝ) : ℂ) ^ 2 /
        (4 * (-I * c))) * f w)) := by
  have hbne (δ : ℝ) : (δ : ℂ) - I * c ≠ 0 := by
    intro h
    have hh := congrArg Complex.im h
    simp at hh
    exact hc.ne' hh
  apply tendsto_integral_filter_of_dominated_convergence (fun w => ‖f w‖)
  · apply Filter.Eventually.of_forall
    intro δ
    exact (by fun_prop : Continuous (fun w : ℝ =>
      Complex.exp (-((2 * Real.pi * w : ℝ) : ℂ) ^ 2 / (4 * ((δ : ℂ) - I * c))))).aestronglyMeasurable.mul hf.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδpos : 0 < δ := hδ
    apply Filter.Eventually.of_forall
    intro w
    have hir : 0 ≤ (((δ : ℂ) - I * c)⁻¹).re := by
      rw [Complex.inv_re]
      exact div_nonneg (by simpa using hδpos.le) (Complex.normSq_nonneg _)
    have hre : (-((2 * Real.pi * w : ℝ) : ℂ) ^ 2 /
        (4 * ((δ : ℂ) - I * c))).re =
        -((2 * Real.pi * w) ^ 2) * (((δ : ℂ) - I * c)⁻¹).re / 4 := by
      have hnum : -((2 * Real.pi * w : ℝ) : ℂ) ^ 2 =
          ((-((2 * Real.pi * w) ^ 2) : ℝ) : ℂ) := by push_cast; rfl
      rw [hnum, div_eq_mul_inv, mul_inv_rev,
        show (4 : ℂ)⁻¹ = ((1 / 4 : ℝ) : ℂ) by norm_num]
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, mul_zero, sub_zero]
      ring
    have hn : ‖Complex.exp (-((2 * Real.pi * w : ℝ) : ℂ) ^ 2 /
        (4 * ((δ : ℂ) - I * c)))‖ ≤ 1 := by
      rw [Complex.norm_exp, Real.exp_le_one_iff, hre]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) hir) (by norm_num)
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans_eq (one_mul _)
  · exact hf.norm
  · apply Filter.Eventually.of_forall
    intro w
    have hh : ContinuousAt (fun δ : ℝ =>
      Complex.exp (-((2 * Real.pi * w : ℝ) : ℂ) ^ 2 / (4 * ((δ : ℂ) - I * c))) * f w) 0 := by
      fun_prop (disch := exact mul_ne_zero (by norm_num) (hbne 0))
    simpa using hh.tendsto.mono_left nhdsWithin_le_nhds

theorem gaussian_prefactor_limit (c : ℝ) (hc : 0 < c) :
    Tendsto (fun δ : ℝ => ((Real.pi : ℂ) / ((δ : ℂ) - I * c)) ^ (1 / 2 : ℂ))
      (nhdsWithin 0 (Ioi 0))
      (𝓝 (((Real.pi : ℂ) / (-I * c)) ^ (1 / 2 : ℂ))) := by
  have hn : (0 : ℂ) - I * c ≠ 0 := by
    simpa using mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne')
  have hr : (Real.pi : ℂ) / (-I * c) = ((Real.pi / c : ℝ) : ℂ) * I := by
    push_cast
    field_simp
    simp [Complex.I_sq]
    rw [div_eq_mul_inv]
    ring
  have hs : (Real.pi : ℂ) / (-I * c) ∈ Complex.slitPlane := by
    rw [hr]
    apply Or.inr
    simpa using (div_pos Real.pi_pos hc).ne'
  have ht : Tendsto (fun δ : ℝ => (Real.pi : ℂ) / ((δ : ℂ) - I * c))
      (nhdsWithin 0 (Ioi 0)) (𝓝 ((Real.pi : ℂ) / (-I * c))) := by
    have ht0 : ContinuousAt (fun δ : ℝ => (Real.pi : ℂ) / ((δ : ℂ) - I * c)) 0 :=
      continuousAt_const.div (by fun_prop) hn
    simpa using ht0.tendsto.mono_left nhdsWithin_le_nhds
  exact (continuousAt_cpow_const hs).tendsto.comp ht


open Complex Filter MeasureTheory Set Topology

/-- Differentiation of a quadratic Fourier phase with a Schwartz amplitude.
The integrable derivative bound is |a| w² |f(w)|, uniform in the time parameter. -/
theorem quadratic_phase_integral_hasDerivAt (a b ε : ℝ) (f : SchwartzMap ℝ ℂ) :
    HasDerivAt (fun t : ℝ => ∫ w : ℝ,
      Complex.exp (((a * t * w ^ 2 + b * w : ℝ) : ℂ) * I) * f w)
      (∫ w : ℝ, Complex.exp (((a * ε * w ^ 2 + b * w : ℝ) : ℂ) * I) *
        (((a * w ^ 2 : ℝ) : ℂ) * I) * f w) ε := by
  let F : ℝ → ℝ → ℂ := fun t w =>
    Complex.exp (((a * t * w ^ 2 + b * w : ℝ) : ℂ) * I) * f w
  let D : ℝ → ℝ → ℂ := fun t w =>
    Complex.exp (((a * t * w ^ 2 + b * w : ℝ) : ℂ) * I) *
      (((a * w ^ 2 : ℝ) : ℂ) * I) * f w
  have hn (t w : ℝ) : ‖Complex.exp (((a * t * w ^ 2 + b * w : ℝ) : ℂ) * I)‖ = 1 := by
    exact Complex.norm_exp_ofReal_mul_I _
  have hm (t : ℝ) : AEStronglyMeasurable (F t) := by
    apply Continuous.aestronglyMeasurable
    dsimp [F]
    fun_prop
  have hi : Integrable (F ε) := f.integrable.mono (hm ε) (by
    apply Filter.Eventually.of_forall
    intro w
    dsimp [F]
    rw [norm_mul, hn, one_mul])
  have hdm : AEStronglyMeasurable (D ε) := by
    apply Continuous.aestronglyMeasurable
    dsimp [D]
    fun_prop
  have hb : Integrable (fun w : ℝ => |a| * (w ^ 2 * ‖f w‖)) := by
    convert (f.integrable_pow_mul volume 2).const_mul |a| using 1
    funext w
    simp [Real.norm_eq_abs, sq_abs]
  have hbound : ∀ᵐ w : ℝ, ∀ t ∈ (univ : Set ℝ), ‖D t w‖ ≤ |a| * (w ^ 2 * ‖f w‖) := by
    apply Filter.Eventually.of_forall
    intro w t _
    dsimp [D]
    rw [norm_mul, norm_mul, hn, one_mul, norm_mul]
    simp [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_assoc]
  have hd : ∀ᵐ w : ℝ, ∀ t ∈ (univ : Set ℝ), HasDerivAt (F · w) (D t w) t := by
    apply Filter.Eventually.of_forall
    intro w t _
    have h := ((((hasDerivAt_id t).const_mul a).mul_const (w ^ 2)).add_const (b * w)).ofReal_comp
    have h' := (h.mul_const I).cexp.mul_const (f w)
    simpa only [F, D, id_eq, mul_one] using h'
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := univ) (bound := fun w : ℝ => |a| * (w ^ 2 * ‖f w‖))
    (by simp) (Filter.Eventually.of_forall hm) hi hdm hbound hb hd).2


open Complex MeasureTheory
open scoped FourierTransform RealInnerProductSpace

theorem schwartz_fourier_integral_zero (f : SchwartzMap ℝ ℂ) :
    ∫ w : ℝ, (𝓕 f) w = f 0 := by
  calc
    (∫ w : ℝ, (𝓕 f) w) = 𝓕⁻ ((𝓕 f : SchwartzMap ℝ ℂ) : ℝ → ℂ) 0 := by
      rw [Real.fourierInv_eq']
      simp
    _ = f 0 := by
      rw [← SchwartzMap.fourierInv_coe, FourierTransform.fourierInv_fourier_eq]

theorem schwartz_fourier_second_moment (f : SchwartzMap ℝ ℂ) :
    deriv (deriv (f : ℝ → ℂ)) 0 =
      -(2 * (Real.pi : ℂ)) ^ 2 * ∫ w : ℝ, (w : ℂ) ^ 2 * (𝓕 f) w := by
  let g := SchwartzMap.derivCLM ℂ ℂ f
  let h := SchwartzMap.derivCLM ℂ ℂ g
  have hg (w : ℝ) : (𝓕 g) w = (2 * Real.pi * I * w) * (𝓕 f) w := by
    exact congrFun (Real.fourier_deriv f.integrable f.differentiable g.integrable) w
  have hh (w : ℝ) : (𝓕 h) w = (2 * Real.pi * I * w) * (𝓕 g) w := by
    exact congrFun (Real.fourier_deriv g.integrable g.differentiable h.integrable) w
  have he (w : ℝ) : (𝓕 h) w = -(2 * (Real.pi : ℂ)) ^ 2 * ((w : ℂ) ^ 2 * (𝓕 f) w) := by
    rw [hh, hg]
    ring_nf
    simp [Complex.I_sq]
  change h 0 = _
  rw [← schwartz_fourier_integral_zero h]
  simp_rw [he]
  rw [integral_const_mul]

theorem oscillatory_gaussian_schwartz_pairing (c : ℝ) (hc : 0 < c)
    (ψ : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, Complex.exp (I * c * (x : ℂ) ^ 2) * ψ x) =
      ((Real.pi : ℂ) / (-I * c)) ^ (1 / 2 : ℂ) *
        ∫ w : ℝ, Complex.exp (-((2 * Real.pi * w : ℝ) : ℂ) ^ 2 / (4 * (-I * c))) * (𝓕 ψ) w := by
  have he (δ : ℝ) (hδ : 0 < δ) :
      (∫ x : ℝ, Complex.exp (-((δ : ℂ) - I * c) * (x : ℂ) ^ 2) * ψ x) =
        ((Real.pi : ℂ) / ((δ : ℂ) - I * c)) ^ (1 / 2 : ℂ) *
          ∫ w : ℝ, Complex.exp (-((2 * Real.pi * w : ℝ) : ℂ) ^ 2 /
            (4 * ((δ : ℂ) - I * c))) * (𝓕 ψ) w := by
    have hp : 0 < ((δ : ℂ) - I * c).re := by simpa using hδ
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat, mul_assoc, integral_const_mul]
      using gaussian_schwartz_pairing ((δ : ℂ) - I * c) hp ψ
  have hl := oscillatory_gaussian_abel_limit c ψ ψ.integrable
  have hr := (gaussian_prefactor_limit c hc).mul
    (gaussian_frequency_abel_limit c hc
      ((𝓕 ψ : SchwartzMap ℝ ℂ) : ℝ → ℂ) (𝓕 ψ).integrable)
  have hr' := hr.congr' (by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (he δ hδ).symm)
  exact tendsto_nhds_unique hl hr'

open Feynman1948

private lemma free_step_zero_fourier (ħ m ε : ℝ) (hħ : 0 < ħ) (hm : 0 < m)
    (hε : 0 < ε) (ψ : SchwartzMap ℝ ℂ) :
    stepEvolution ħ m (fun _ => 0) ε ψ 0 =
      ∫ w : ℝ, Complex.exp (((-(2 * Real.pi ^ 2 * ħ / m) * ε * w ^ 2 : ℝ) : ℂ) * I) * (𝓕 ψ) w := by
  let c : ℝ := m / (2 * ħ * ε)
  have hc : 0 < c := div_pos hm (by positivity)
  have hħ0 : (ħ : ℂ) ≠ 0 := by exact_mod_cast hħ.ne'
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hε0 : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have hcoef (y : ℝ) : I * (shortTimeAction m (fun _ => 0) ε 0 y : ℂ) / ħ =
      I * c * (y : ℂ) ^ 2 := by
    dsimp [shortTimeAction, c]
    push_cast
    field_simp [hħ0, hε0]
    ring
  have hratio : (Real.pi : ℂ) / (-I * c) = 2 * Real.pi * ħ * ε * I / m := by
    dsimp [c]
    push_cast
    field_simp [hħ0, hm0, hε0]
    ring_nf
    simp [I_sq]
  have he (w : ℝ) : -((2 * Real.pi * w : ℝ) : ℂ) ^ 2 / (4 * (-I * c)) =
      ((-(2 * Real.pi ^ 2 * ħ / m) * ε * w ^ 2 : ℝ) : ℂ) * I := by
    dsimp [c]
    push_cast
    field_simp [hħ0, hm0, hε0]
    ring_nf
    simp [I_sq]
  have hA : normalizingFactor ħ m ε ≠ 0 := by
    apply cpow_ne_zero_iff.mpr
    left
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) hħ0) hε0) I_ne_zero) hm0
  rw [stepEvolution]
  simp_rw [hcoef]
  rw [oscillatory_gaussian_schwartz_pairing c hc ψ, hratio]
  simp_rw [he]
  change (normalizingFactor ħ m ε)⁻¹ * (normalizingFactor ħ m ε * _) = _
  rw [← mul_assoc, inv_mul_cancel₀ hA, one_mul]

private lemma free_step_zero_first_order (ħ m : ℝ) (hħ : 0 < ħ) (hm : 0 < m)
    (ψ : SchwartzMap ℝ ℂ) :
    Tendsto (fun ε : ℝ => (stepEvolution ħ m (fun _ => 0) ε ψ 0 - ψ 0) / ε)
      (𝓝[>] 0) (𝓝 (I * ħ / (2 * m) * deriv (deriv ψ) 0)) := by
  let a : ℝ := -(2 * Real.pi ^ 2 * ħ / m)
  let f : ℝ → ℂ := fun ε => ∫ w : ℝ,
    Complex.exp (((a * ε * w ^ 2 : ℝ) : ℂ) * I) * (𝓕 ψ) w
  have hdiff := quadratic_phase_integral_hasDerivAt a 0 0 (𝓕 ψ)
  have hdiff' : HasDerivAt f
      (((a : ℂ) * I) * ∫ w : ℝ, (w : ℂ) ^ 2 * (𝓕 ψ) w) 0 := by
    simp only [mul_zero, zero_mul, add_zero, Complex.ofReal_zero,
      Complex.exp_zero, one_mul] at hdiff
    have he (w : ℝ) : (((a * w ^ 2 : ℝ) : ℂ) * I) * (𝓕 ψ) w =
        ((a : ℂ) * I) * ((w : ℂ) ^ 2 * (𝓕 ψ) w) := by push_cast; ring
    simp_rw [he, integral_const_mul] at hdiff
    exact hdiff
  have hf0 : f 0 = ψ 0 := by
    simpa [f] using schwartz_fourier_integral_zero ψ
  have hv : ((a : ℂ) * I) * (∫ w : ℝ, (w : ℂ) ^ 2 * (𝓕 ψ) w) =
      I * ħ / (2 * m) * deriv (deriv ψ) 0 := by
    rw [schwartz_fourier_second_moment]
    dsimp [a]
    push_cast
    ring
  rw [hv] at hdiff'
  have ht := hdiff'.tendsto_slope_zero_right
  have ht' : Tendsto (fun ε : ℝ => (f ε - ψ 0) / (ε : ℂ))
      (𝓝[>] 0) (𝓝 (I * ħ / (2 * m) * deriv (deriv ψ) 0)) := by
    simpa only [zero_add, hf0, RCLike.real_smul_eq_coe_mul,
      RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using ht
  apply ht'.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [free_step_zero_fourier ħ m ε hħ hm hε ψ]

theorem solution (ħ m : ℝ) (hħ : 0 < ħ) (hm : 0 < m)
    (ψ : SchwartzMap ℝ ℂ) (x : ℝ) :
    Tendsto (fun ε : ℝ => (stepEvolution ħ m (fun _ => 0) ε ψ x - ψ x) / ε)
      (𝓝[>] 0) (𝓝 (I * ħ / (2 * m) * deriv (deriv ψ) x)) := by
  let φ := ψ.compSubConstCLM ℂ (-x)
  have hφ (y : ℝ) : φ y = ψ (y + x) := by simp [φ]
  have hderiv : deriv (deriv (φ : ℝ → ℂ)) 0 = deriv (deriv (ψ : ℝ → ℂ)) x := by
    have hfun : (φ : ℝ → ℂ) = fun y => ψ (y + x) := funext hφ
    rw [hfun]
    have hdfun : deriv (fun y : ℝ => ψ (y + x)) = fun y => deriv ψ (y + x) :=
      funext (fun y => deriv_comp_add_const (ψ : ℝ → ℂ) x y)
    rw [hdfun, deriv_comp_add_const]
    simp
  have he (ε : ℝ) : stepEvolution ħ m (fun _ => 0) ε φ 0 =
      stepEvolution ħ m (fun _ => 0) ε ψ x := by
    rw [stepEvolution, stepEvolution]
    congr 1
    rw [← integral_add_right_eq_self (fun y : ℝ =>
      Complex.exp (I * (shortTimeAction m (fun _ => 0) ε x y : ℂ) / ħ) * ψ y) x]
    apply integral_congr_ae
    filter_upwards [] with y
    rw [hφ]
    have ha : shortTimeAction m (fun _ => 0) ε 0 y =
        shortTimeAction m (fun _ => 0) ε x (y + x) := by
      dsimp [shortTimeAction]
      ring
    rw [ha]
  have ht := free_step_zero_first_order ħ m hħ hm φ
  rw [hderiv] at ht
  simpa only [he, hφ, zero_add] using ht

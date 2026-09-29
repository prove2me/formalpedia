-- Prove2me | solution 1 for DeBruijnNewman.Dobner.xi_zero_eq_gamma_zeta
-- status  : ACCEPTED   (prove)
-- author  : @adobner
-- created : 2026-09-24T23:41:30.666658+00:00
-- url     : https://prove2.me/submissions/1f6f75f0-6b55-4d9c-8894-06408e7b56b7

import Definitions.Def_DeBruijnNewman_Dobner

open MeasureTheory Set Filter DeBruijnNewman DeBruijnNewman.Dobner
open HurwitzKernelBounds
open scoped Topology

private theorem theta_moment_deriv (k : ℕ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (F_nat k 1) (-Real.pi * F_nat (k + 2) 1 x) x := by
  have hd (n : ℕ) (y : ℝ) :
      HasDerivAt (fun y => f_nat k 1 y n)
        (-Real.pi * f_nat (k + 2) 1 y n) y := by
    convert! (((hasDerivAt_id y).const_mul
      (-Real.pi * ((n : ℝ) + 1) ^ 2)).exp.const_mul (((n : ℝ) + 1) ^ k)) using 1
    simp only [f_nat, pow_add, id_eq]
    ring
  have hb (n : ℕ) (y : ℝ) (hy : y ∈ Ioi (x / 2)) :
      ‖-Real.pi * f_nat (k + 2) 1 y n‖ ≤
        Real.pi * f_nat (k + 2) 1 (x / 2) n := by
    simp only [norm_mul, norm_neg, Real.norm_of_nonneg Real.pi_pos.le]
    rw [Real.norm_of_nonneg (by unfold f_nat; positivity)]
    unfold f_nat
    apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hy.le
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) (sq_nonneg _))
  have ht := hasDerivAt_tsum_of_isPreconnected
    ((summable_f_nat (k + 2) 1 (show 0 < x / 2 by positivity)).mul_left Real.pi)
    isOpen_Ioi (convex_Ioi (x / 2)).isPreconnected
    (fun n y _ => hd n y) hb (show x ∈ Ioi (x / 2) by change x / 2 < x; linarith)
    (summable_f_nat k 1 hx) (show x ∈ Ioi (x / 2) by change x / 2 < x; linarith)
  simpa only [F_nat, tsum_mul_left] using! ht

private theorem theta_zero_kernel (x : ℝ) (hx : 0 < x) :
    1 + 2 * F_nat 0 1 x = HurwitzZeta.evenKernel 0 x := by
  have h : 2 * F_nat 0 1 x = HurwitzZeta.evenKernel 0 x - 1 := by
    simpa [F_nat, f_nat, tsum_mul_left,
      ← HurwitzZeta.evenKernel_eq_cosKernel_of_zero] using
      (HurwitzZeta.hasSum_nat_cosKernel₀ 0 hx).tsum_eq
  linarith

private noncomputable def symmetricTheta (u : ℝ) : ℝ :=
  Real.exp u * (1 + 2 * F_nat 0 1 (Real.exp (4 * u)))

private noncomputable def symmetricTheta' (u : ℝ) : ℝ :=
  symmetricTheta u -
    8 * Real.pi * Real.exp (5 * u) * F_nat 2 1 (Real.exp (4 * u))

private theorem symmetricTheta_even (u : ℝ) :
    symmetricTheta (-u) = symmetricTheta u := by
  simp only [symmetricTheta, theta_zero_kernel _ (Real.exp_pos _)]
  have h := HurwitzZeta.evenKernel_functional_equation 0 (Real.exp (4 * u))
  rw [← HurwitzZeta.evenKernel_eq_cosKernel_of_zero,
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp] at h
  have he : 1 / Real.exp (4 * u) = Real.exp (4 * -u) := by
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  rw [he] at h
  rw [h, ← mul_assoc, one_div, ← Real.exp_neg, ← Real.exp_add]
  congr 2
  ring

private theorem symmetricTheta_deriv (u : ℝ) :
    HasDerivAt symmetricTheta (symmetricTheta' u) u := by
  have he := ((hasDerivAt_id u).const_mul 4).exp
  have hθ := (theta_moment_deriv 0 (Real.exp (4 * u)) (Real.exp_pos _)).comp u he
  have hd := (Real.hasDerivAt_exp u).mul ((hθ.const_mul 2).const_add 1)
  convert! hd using 1
  dsimp [symmetricTheta', symmetricTheta]
  norm_num only at *
  have he5 : Real.exp (5 * u) = Real.exp u * Real.exp (4 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he5]
  ring

private theorem phi_theta_moments (u : ℝ) :
    Phi u = 2 * Real.pi ^ 2 * Real.exp (9 * u) * F_nat 4 1 (Real.exp (4 * u)) -
      3 * Real.pi * Real.exp (5 * u) * F_nat 2 1 (Real.exp (4 * u)) := by
  have h4 := (summable_f_nat 4 1 (Real.exp_pos (4 * u))).mul_left
    (2 * Real.pi ^ 2 * Real.exp (9 * u))
  have h2 := (summable_f_nat 2 1 (Real.exp_pos (4 * u))).mul_left
    (3 * Real.pi * Real.exp (5 * u))
  rw [Phi, F_nat, F_nat, ← tsum_mul_left, ← tsum_mul_left, ← h4.tsum_sub h2]
  apply tsum_congr
  intro n
  simp only [f_nat, neg_mul]
  ring

private theorem symmetricTheta_second_deriv (u : ℝ) :
    HasDerivAt symmetricTheta' (symmetricTheta u + 16 * Phi u) u := by
  have he4 := ((hasDerivAt_id u).const_mul 4).exp
  have he5 := ((hasDerivAt_id u).const_mul 5).exp
  have hθ := (theta_moment_deriv 2 (Real.exp (4 * u)) (Real.exp_pos _)).comp u he4
  have hd := (symmetricTheta_deriv u).sub ((he5.const_mul (8 * Real.pi)).mul hθ)
  convert! hd using 1
  dsimp [symmetricTheta']
  norm_num only at *
  rw [phi_theta_moments]
  have he9 : Real.exp (9 * u) = Real.exp (5 * u) * Real.exp (4 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he9]
  ring

private theorem phi_even (u : ℝ) : Phi (-u) = Phi u := by
  have hd (x : ℝ) : -symmetricTheta' (-x) = symmetricTheta' x := by
    have h := (symmetricTheta_deriv (-x)).comp x (hasDerivAt_neg x)
    have hh : (fun x => symmetricTheta (-x)) = symmetricTheta :=
      funext symmetricTheta_even
    simp only [Function.comp_def] at h
    rw [hh] at h
    simpa using h.unique (symmetricTheta_deriv x)
  have h := ((symmetricTheta_second_deriv (-u)).comp u (hasDerivAt_neg u)).neg
  have hh : (fun x => -symmetricTheta' (-x)) = symmetricTheta' := funext hd
  change HasDerivAt (fun x => -symmetricTheta' (-x)) _ u at h
  rw [hh] at h
  have heq := h.unique (symmetricTheta_second_deriv u)
  rw [symmetricTheta_even] at heq
  linarith

private theorem exp_cpow_factor (z : ℂ) (u : ℝ) :
    (Real.exp u : ℂ) * (Real.exp u : ℂ) ^ (z - 1) = Complex.exp (z * (u : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
    ← Complex.ofReal_log (Real.exp_nonneg _), Real.log_exp, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  ring

private theorem mellin_eq_exp_integral (f : ℝ → ℂ) (z : ℂ) :
    mellin f z = ∫ u : ℝ, Complex.exp (z * (u : ℂ)) * f (Real.exp u) := by
  have hi : Real.exp '' (univ : Set ℝ) = Ioi 0 := by
    rw [image_univ, Real.range_exp]
  rw [mellin, ← hi, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn]
  simp only [Real.abs_exp, Complex.real_smul, smul_eq_mul, ← mul_assoc, exp_cpow_factor,
    setIntegral_univ]

private theorem mellin_integrable_exp (f : ℝ → ℂ) (z : ℂ) (hf : MellinConvergent f z) :
    Integrable (fun u : ℝ => Complex.exp (z * (u : ℂ)) * f (Real.exp u)) := by
  have hi : Real.exp '' (univ : Set ℝ) = Ioi 0 := by
    rw [image_univ, Real.range_exp]
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn
    (fun x : ℝ => (x : ℂ) ^ (z - 1) * f x)).mp (by simpa [hi, MellinConvergent] using hf)
  simpa only [Real.abs_exp, Complex.real_smul, ← mul_assoc, exp_cpow_factor,
    integrableOn_univ] using! h

private noncomputable def expMode (z : ℂ) (b u : ℝ) : ℂ :=
  Complex.exp ((4 * z) * (u : ℂ)) * (Real.exp (-b * Real.exp (4 * u)) : ℂ)

private theorem exp_mode_integrable (z : ℂ) (hz : 0 < z.re) (b : ℝ) (hb : 0 < b) :
    Integrable (expMode z b) := by
  have hg : MellinConvergent (fun x : ℝ => (Real.exp (-x) : ℂ)) z := by
    simpa only [MellinConvergent, smul_eq_mul, mul_comm] using Complex.GammaIntegral_convergent hz
  have hgb := (MellinConvergent.comp_mul_left (f := fun x : ℝ => (Real.exp (-x) : ℂ))
    (s := z) hb).mpr hg
  have h := (mellin_integrable_exp _ z hgb).comp_mul_left' (R := 4) (by norm_num)
  convert! h using 1
  ext u
  simp only [expMode, Complex.ofReal_mul, Complex.ofReal_ofNat, neg_mul]
  congr 2
  ring

private theorem exp_mode_integral (z : ℂ) (hz : 0 < z.re) (b : ℝ) (hb : 0 < b) :
    ∫ u : ℝ, expMode z b u = (1 / 4 : ℂ) * (b : ℂ) ^ (-z) * Complex.Gamma z := by
  have hs : expMode z b = fun u : ℝ =>
      Complex.exp (z * ((4 * u : ℝ) : ℂ)) * (Real.exp (-b * Real.exp (4 * u)) : ℂ) := by
    ext u
    dsimp [expMode]
    push_cast
    congr 2
    ring
  rw [hs, Measure.integral_comp_mul_left
    (fun v : ℝ => Complex.exp (z * (v : ℂ)) * (Real.exp (-b * Real.exp v) : ℂ)) 4,
    ← mellin_eq_exp_integral (fun x : ℝ => (Real.exp (-b * x) : ℂ)) z]
  have hm : mellin (fun x : ℝ => (Real.exp (-b * x) : ℂ)) z =
      (b : ℂ) ^ (-z) * Complex.Gamma z := by
    have hg : mellin (fun x : ℝ => (Real.exp (-x) : ℂ)) z = Complex.Gamma z := by
      rw [Complex.Gamma_eq_integral hz]
      simp only [mellin, Complex.GammaIntegral, smul_eq_mul, mul_comm]
    simpa only [neg_mul, smul_eq_mul, hg] using
      (mellin_comp_mul_left (fun x : ℝ => (Real.exp (-x) : ℂ)) z hb)
  rw [hm]
  norm_num [Complex.real_smul]
  ring

private noncomputable def weightedMode (k : ℕ) (s : ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  ((n : ℂ) + 1) ^ (2 * k) *
    expMode (s / 2 + (k : ℂ)) (Real.pi * ((n : ℝ) + 1) ^ 2) u

private noncomputable def modeCoefficient (k : ℕ) (s : ℂ) : ℂ :=
  (1 / 4 : ℂ) * (Real.pi : ℂ) ^ (-(s / 2 + (k : ℂ))) * Complex.Gamma (s / 2 + (k : ℂ))

private theorem weighted_mode_integrable (k : ℕ) (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    Integrable (weightedMode k s n) := by
  apply Integrable.const_mul
  apply exp_mode_integrable
  · simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
    positivity
  · positivity

private theorem weighted_mode_integral (k : ℕ) (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    ∫ u : ℝ, weightedMode k s n u =
      modeCoefficient k s * (1 / ((n : ℂ) + 1) ^ s) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hn0 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast hn.ne'
  simp only [weightedMode]
  rw [integral_const_mul, exp_mode_integral _
    (by simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]; positivity)
    _ (by positivity)]
  have hp : ((Real.pi * ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) ^ (-(s / 2 + (k : ℂ))) =
      (Real.pi : ℂ) ^ (-(s / 2 + (k : ℂ))) *
        ((n : ℂ) + 1) ^ (-(s + (2 * k : ℕ))) := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le (sq_nonneg _)]
    congr 1
    rw [← Real.rpow_two, ← Complex.cpow_mul_ofReal_nonneg hn.le]
    push_cast
    congr 1
    ring
  rw [hp]
  have hc : ((n : ℂ) + 1) ^ (2 * k) * ((n : ℂ) + 1) ^ (-(s + (2 * k : ℕ))) =
      1 / ((n : ℂ) + 1) ^ s := by
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hn0]
    rw [show ((2 * k : ℕ) : ℂ) + -(s + ((2 * k : ℕ) : ℂ)) = -s by ring,
      Complex.cpow_neg, one_div]
  dsimp [modeCoefficient]
  calc
    _ = ((1 / 4 : ℂ) * (Real.pi : ℂ) ^ (-(s / 2 + (k : ℂ))) *
        Complex.Gamma (s / 2 + (k : ℂ))) *
        (((n : ℂ) + 1) ^ (2 * k) * ((n : ℂ) + 1) ^ (-(s + (2 * k : ℕ)))) := by ring
    _ = _ := by rw [hc]

private theorem zeta_hasSum (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) (riemannZeta s) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  apply Summable.hasSum
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℂ) ^ s) 1).mpr
      (Complex.summable_one_div_nat_cpow.mpr hs)

private theorem weighted_mode_norm (k : ℕ) (s : ℂ) (n : ℕ) (u : ℝ) :
    ‖weightedMode k s n u‖ = (weightedMode k (s.re : ℂ) n u).re := by
  have hN : (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
  simp only [weightedMode, expMode, hN, norm_mul, norm_pow, Complex.norm_exp,
    Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity),
    Real.norm_of_nonneg (Real.exp_nonneg _), ← Complex.ofReal_pow,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.natCast_re, Complex.natCast_im, Complex.exp_re, mul_zero, zero_mul,
    add_zero, sub_zero, zero_div]
  norm_num

private theorem weighted_mode_norm_summable (k : ℕ) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n : ℕ => ∫ u : ℝ, ‖weightedMode k s n u‖) := by
  have hsr : 0 < (s.re : ℂ).re := by simpa using (lt_trans zero_lt_one hs)
  have h (n : ℕ) : (∫ u : ℝ, ‖weightedMode k s n u‖) =
      (modeCoefficient k (s.re : ℂ) * (1 / ((n : ℂ) + 1) ^ (s.re : ℂ))).re := by
    simp only [weighted_mode_norm]
    have hr := integral_re (weighted_mode_integrable k (s.re : ℂ) hsr n)
    change (∫ u : ℝ, (weightedMode k (s.re : ℂ) n u).re) =
      (∫ u : ℝ, weightedMode k (s.re : ℂ) n u).re at hr
    rw [hr, weighted_mode_integral k (s.re : ℂ) hsr n]
  simp only [h]
  exact (((zeta_hasSum (s.re : ℂ) (by simpa using hs)).mul_left
    (modeCoefficient k (s.re : ℂ))).map Complex.reCLM Complex.reCLM.continuous).summable

private theorem integrable_series {F : ℕ → ℝ → ℂ}
    (hm : ∀ n, Measurable (F n)) (hi : ∀ n, Integrable (F n))
    (hs : Summable (fun n => ∫ u : ℝ, ‖F n u‖)) :
    Integrable (fun u : ℝ => ∑' n, F n u) := by
  refine ⟨(Measurable.tsum hm).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  apply lt_of_le_of_lt (lintegral_mono (fun u => enorm_tsum_le_tsum_enorm)) _
  rw [lintegral_tsum (fun n => (hm n).enorm.aemeasurable)]
  simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hi _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg (fun u => norm_nonneg _)) hs]
  exact ENNReal.ofReal_lt_top

private theorem weighted_series_integrable (k : ℕ) (s : ℂ) (hs : 1 < s.re) :
    Integrable (fun u : ℝ => ∑' n, weightedMode k s n u) := by
  apply integrable_series
  · intro n
    unfold weightedMode expMode
    fun_prop
  · exact weighted_mode_integrable k s (lt_trans zero_lt_one hs)
  · exact weighted_mode_norm_summable k s hs

private theorem weighted_series_integral (k : ℕ) (s : ℂ) (hs : 1 < s.re) :
    ∫ u : ℝ, ∑' n, weightedMode k s n u = modeCoefficient k s * riemannZeta s := by
  have h := hasSum_integral_of_summable_integral_norm
    (weighted_mode_integrable k s (lt_trans zero_lt_one hs))
    (weighted_mode_norm_summable k s hs)
  simp only [weighted_mode_integral k s (lt_trans zero_lt_one hs)] at h
  exact h.unique ((zeta_hasSum s hs).mul_left (modeCoefficient k s))

private theorem weighted_series_eq (k : ℕ) (s : ℂ) (u : ℝ) :
    (∑' n, weightedMode k s n u) =
      (F_nat (2 * k) 1 (Real.exp (4 * u)) : ℂ) *
        Complex.exp ((2 * s + 4 * (k : ℂ)) * (u : ℂ)) := by
  rw [F_nat, Complex.ofReal_tsum, ← tsum_mul_right]
  apply tsum_congr
  intro n
  simp only [weightedMode, expMode, f_nat, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one, neg_mul]
  have he : 4 * (s / 2 + (k : ℂ)) = 2 * s + 4 * (k : ℂ) := by ring
  rw [he]
  ring

private theorem phi_laplace_series (s : ℂ) (u : ℝ) :
    (Phi u : ℂ) * Complex.exp ((2 * s - 1) * (u : ℂ)) =
      (2 * (Real.pi : ℂ) ^ 2) * (∑' n, weightedMode 2 s n u) -
        (3 * (Real.pi : ℂ)) * (∑' n, weightedMode 1 s n u) := by
  have he (r : ℝ) :
      Complex.exp ((2 * s - 1 + (r : ℂ)) * (u : ℂ)) =
        (Real.exp (r * u) : ℂ) * Complex.exp ((2 * s - 1) * (u : ℂ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    push_cast
    congr 1
    ring
  have h9 : 2 * s + 4 * (2 : ℂ) = 2 * s - 1 + (9 : ℝ) := by push_cast; ring
  have h5 : 2 * s + 4 = 2 * s - 1 + (5 : ℝ) := by push_cast; ring
  simp only [weighted_series_eq, Nat.cast_ofNat, Nat.cast_one, mul_one,
    h9, h5, he, phi_theta_moments]
  norm_num only
  push_cast
  ring

private theorem phi_laplace_integrable (s : ℂ) (hs : 1 < s.re) :
    Integrable (fun u : ℝ => (Phi u : ℂ) * Complex.exp ((2 * s - 1) * (u : ℂ))) := by
  simp only [phi_laplace_series]
  exact ((weighted_series_integrable 2 s hs).const_mul _).sub
    ((weighted_series_integrable 1 s hs).const_mul _)

private theorem mode_coefficients_combine (s : ℂ) (hs : 0 < s.re) :
    2 * (Real.pi : ℂ) ^ 2 * modeCoefficient 2 s -
      3 * (Real.pi : ℂ) * modeCoefficient 1 s = (1 / 4 : ℂ) * gammaFactor s := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hp (k : ℕ) :
      (Real.pi : ℂ) ^ k * (Real.pi : ℂ) ^ (-(s / 2 + (k : ℂ))) =
        (Real.pi : ℂ) ^ (-(s / 2)) := by
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hpi]
    congr 1
    ring
  have hs0 : s / 2 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.div_ofNat_re, Complex.zero_re] at this
    linarith
  have hs1 : s / 2 + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.zero_re] at this
    linarith
  have hg2 : Complex.Gamma (s / 2 + 2) =
      (s / 2 + 1) * (s / 2) * Complex.Gamma (s / 2) := by
    rw [show s / 2 + 2 = (s / 2 + 1) + 1 by ring,
      Complex.Gamma_add_one _ hs1, Complex.Gamma_add_one _ hs0]
    ring
  have he : (Real.pi : ℂ) ^ (-(s / 2)) =
      Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hpi, ← Complex.ofReal_log Real.pi_pos.le]
    congr 1
    ring
  calc
    _ = (1 / 2 : ℂ) *
        ((Real.pi : ℂ) ^ 2 * (Real.pi : ℂ) ^ (-(s / 2 + (2 : ℕ)))) *
        Complex.Gamma (s / 2 + 2) -
      (3 / 4 : ℂ) *
        ((Real.pi : ℂ) ^ 1 * (Real.pi : ℂ) ^ (-(s / 2 + (1 : ℕ)))) *
        Complex.Gamma (s / 2 + 1) := by
      simp only [modeCoefficient, Nat.cast_ofNat, Nat.cast_one, pow_one]
      ring
    _ = _ := by
      rw [hp 2, hp 1, hg2, Complex.Gamma_add_one _ hs0, he]
      unfold gammaFactor
      ring

private theorem phi_laplace_integral (s : ℂ) (hs : 1 < s.re) :
    ∫ u : ℝ, (Phi u : ℂ) * Complex.exp ((2 * s - 1) * (u : ℂ)) =
      (1 / 4 : ℂ) * gammaFactor s * riemannZeta s := by
  simp only [phi_laplace_series]
  rw [integral_sub ((weighted_series_integrable 2 s hs).const_mul _)
    ((weighted_series_integrable 1 s hs).const_mul _),
    integral_const_mul, integral_const_mul, weighted_series_integral 2 s hs,
    weighted_series_integral 1 s hs, ← mul_assoc, ← mul_assoc, ← sub_mul,
    mode_coefficients_combine s (lt_trans zero_lt_one hs)]

private theorem cosine_exp_split (s : ℂ) (u : ℝ) :
    Complex.cos (-Complex.I * (2 * s - 1) * (u : ℂ)) =
      (Complex.exp ((2 * s - 1) * (u : ℂ)) +
        Complex.exp ((2 * s - 1) * ((-u : ℝ) : ℂ))) / 2 := by
  have hp : (-Complex.I * (2 * s - 1) * (u : ℂ)) * Complex.I =
      (2 * s - 1) * (u : ℂ) := by
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hm : -(-Complex.I * (2 * s - 1) * (u : ℂ)) * Complex.I =
      (2 * s - 1) * ((-u : ℝ) : ℂ) := by
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [Complex.cos, hp, hm]

private theorem laplace_eq_twice_H (s : ℂ) (hs : 1 < s.re) :
    (∫ u : ℝ, (Phi u : ℂ) * Complex.exp ((2 * s - 1) * (u : ℂ))) =
      2 * H 0 (-Complex.I * (2 * s - 1)) := by
  let f : ℝ → ℂ := fun u => (Phi u : ℂ) * Complex.exp ((2 * s - 1) * (u : ℂ))
  have hf : Integrable f := phi_laplace_integrable s hs
  have hn : Integrable (fun u : ℝ => f (-u)) := by
    simpa only [neg_one_mul] using hf.comp_mul_left' (R := -1) (by norm_num)
  have hneg : (∫ u in Iic (0 : ℝ), f u) = ∫ u in Ioi (0 : ℝ), f (-u) := by
    simpa only [neg_zero] using (integral_comp_neg_Ioi 0 f).symm
  calc
    _ = (∫ u in Iic (0 : ℝ), f u) + ∫ u in Ioi (0 : ℝ), f u :=
      (intervalIntegral.integral_Iic_add_Ioi hf.integrableOn hf.integrableOn).symm
    _ = ∫ u in Ioi (0 : ℝ), f u + f (-u) := by
      rw [hneg, integral_add hf.integrableOn hn.integrableOn]
      ring
    _ = _ := by
      simp only [H, zero_mul, Real.exp_zero, one_mul]
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _
      dsimp [f]
      rw [phi_even, cosine_exp_split]
      ring

theorem solution (s : ℂ) (hs : 1 < s.re) :
    DeBruijnNewman.Dobner.xiT 0 s =
      DeBruijnNewman.Dobner.gammaFactor s * riemannZeta s := by
  have h := (laplace_eq_twice_H s hs).symm.trans (phi_laplace_integral s hs)
  unfold xiT
  linear_combination 4 * h

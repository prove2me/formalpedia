-- Prove2me | solution 1 for DeBruijnNewman.Dobner.mellin_series_representation
-- status  : ACCEPTED   (prove)
-- author  : @adobner
-- created : 2026-09-24T22:54:56.546905+00:00
-- url     : https://prove2.me/submissions/4020f1d8-147f-4f3c-93e5-b5838b7c2dce

import Definitions.Def_DeBruijnNewman_Dobner_Mellin
import Theorems.Thm_DeBruijnNewman_Dobner_gaussian_convolution
import Theorems.Thm_DeBruijnNewman_Dobner_xi_zero_eq_gamma_zeta

open MeasureTheory Set Filter DeBruijnNewman DeBruijnNewman.Dobner
open scoped Topology

private noncomputable def contourPoint (v : ℝ) : ℂ := 2 + (v : ℂ) * Complex.I

private noncomputable def gaussianKernel (T : ℝ) (w : ℂ) (v : ℝ) : ℂ :=
  Complex.exp ((w - contourPoint v) ^ 2 / (T : ℂ))

private theorem gamma_line_norm (v : ℝ) :
    ‖Complex.Gamma (contourPoint v / 2)‖ ≤ 1 := by
  have hre : (contourPoint v / 2).re = 1 := by
    norm_num [contourPoint, Complex.div_re]
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi 0) := by
    simpa using Real.GammaIntegral_convergent (s := 1) zero_lt_one
  have heq : ∫ x : ℝ in Ioi 0, Real.exp (-x) = 1 := by
    simpa using (Real.Gamma_eq_integral (s := 1) zero_lt_one).symm
  rw [Complex.Gamma_eq_integral (by rw [hre]; norm_num), Complex.GammaIntegral]
  rw [← heq]
  apply norm_integral_le_of_norm_le hint
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _),
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp [hre]

private theorem gamma_factor_norm_bound (v : ℝ) :
    ‖gammaFactor (contourPoint v)‖ ≤
      (9 + v ^ 2) * Real.exp (-Real.log Real.pi) := by
  have hv : ‖contourPoint v‖ ≤ 2 + |v| := by
    simpa [contourPoint, norm_mul] using norm_add_le (2 : ℂ) ((v : ℂ) * Complex.I)
  have hv1 : ‖contourPoint v - 1‖ ≤ 3 + |v| := by
    have h := norm_sub_le (contourPoint v) (1 : ℂ)
    norm_num at h
    linarith
  have he : ‖Complex.exp (-(contourPoint v / 2) * (Real.log Real.pi : ℂ))‖ =
      Real.exp (-Real.log Real.pi) := by
    rw [Complex.norm_exp]
    congr 1
    norm_num [contourPoint, Complex.mul_re, Complex.div_re]
  unfold gammaFactor
  rw [norm_mul, norm_mul, norm_div, norm_mul, Complex.norm_ofNat, he]
  calc
    _ ≤ (((2 + |v|) * (3 + |v|)) / 2 * Real.exp (-Real.log Real.pi)) * 1 := by
      gcongr
      exact gamma_line_norm v
    _ ≤ (9 + v ^ 2) * Real.exp (-Real.log Real.pi) := by
      rw [mul_one]
      gcongr
      nlinarith [sq_nonneg (|v| - 3), sq_abs v, abs_nonneg v]

private theorem gamma_factor_continuous_on_line :
    Continuous (fun v : ℝ => gammaFactor (contourPoint v)) := by
  have hG : Continuous (fun v : ℝ => Complex.Gamma (contourPoint v / 2)) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    apply (Complex.differentiableAt_Gamma (contourPoint v / 2) ?_).continuousAt.comp
      (f := fun r : ℝ => contourPoint r / 2) (by unfold contourPoint; fun_prop)
    intro n hn
    have h := congrArg Complex.re hn
    norm_num [contourPoint, Complex.div_re] at h
    linarith [Nat.cast_nonneg (α := ℝ) n]
  unfold gammaFactor contourPoint at *
  fun_prop

private theorem kernel_norm (T : ℝ) (w : ℂ) (v : ℝ) :
    ‖gaussianKernel T w v‖ =
      Real.exp (((w.re - 2) ^ 2 - (w.im - v) ^ 2) / T) := by
  rw [gaussianKernel, Complex.norm_exp, Complex.div_ofReal_re]
  congr 1
  norm_num [contourPoint, sq, Complex.mul_re, Complex.mul_im]

private theorem gaussian_polynomial_integrable (T : ℝ) (hT : 0 < T) (y : ℝ) :
    Integrable (fun v : ℝ =>
      (9 + v ^ 2) * Real.exp (-((v - y) ^ 2) / T)) := by
  have hbase : Integrable (fun v : ℝ => Real.exp (-v ^ 2 / T)) := by
    simpa only [neg_mul, mul_neg, div_eq_mul_inv, mul_comm] using
      (integrable_exp_neg_mul_sq (inv_pos.mpr hT))
  have hpoly : Integrable (fun v : ℝ => v ^ 2 * Real.exp (-v ^ 2 / T)) := by
    simpa only [Real.rpow_two, neg_mul, mul_neg, div_eq_mul_inv, mul_comm] using
      (integrable_rpow_mul_exp_neg_mul_sq (inv_pos.mpr hT) (s := 2) (by norm_num))
  have hb := ((hbase.const_mul (9 + 2 * y ^ 2)).add (hpoly.const_mul 2)).comp_sub_right y
  apply hb.mono' (by fun_prop)
  filter_upwards with v
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (9 + (2 * y ^ 2 + 2 * (v - y) ^ 2)) *
        Real.exp (-((v - y) ^ 2) / T) := by
      gcongr
      nlinarith [sq_nonneg (v - 2 * y)]
    _ = _ := by simp only [Pi.add_apply]; ring

private theorem gamma_kernel_integrable (T : ℝ) (hT : 0 < T) (w : ℂ) :
    Integrable (fun v : ℝ => gammaFactor (contourPoint v) * gaussianKernel T w v) := by
  have hb := (gaussian_polynomial_integrable T hT w.im).const_mul
    (Real.exp (-Real.log Real.pi) * Real.exp ((w.re - 2) ^ 2 / T))
  apply hb.mono'
  · have := gamma_factor_continuous_on_line
    unfold gaussianKernel contourPoint
    fun_prop
  · filter_upwards with v
    rw [norm_mul, kernel_norm]
    calc
      _ ≤ ((9 + v ^ 2) * Real.exp (-Real.log Real.pi)) *
          Real.exp (((w.re - 2) ^ 2 - (w.im - v) ^ 2) / T) := by
        gcongr
        exact gamma_factor_norm_bound v
      _ = _ := by
        rw [show ((w.re - 2) ^ 2 - (w.im - v) ^ 2) / T =
          (w.re - 2) ^ 2 / T + -((v - w.im) ^ 2) / T by ring, Real.exp_add]
        ring

private theorem dirichlet_term_eq (s : ℂ) (n : ℕ) :
    Complex.exp (-s * (Real.log ((n : ℝ) + 1) : ℂ)) =
      1 / ((n : ℂ) + 1) ^ s := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hn' : (n : ℂ) + 1 ≠ 0 := by
    exact_mod_cast hn.ne'
  have hlog : Complex.log ((n : ℂ) + 1) =
      (Real.log ((n : ℝ) + 1) : ℂ) := by
    rw [show (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_log hn.le]
  rw [Complex.cpow_def_of_ne_zero hn', hlog, one_div, ← Complex.exp_neg]
  congr 1
  ring

private theorem zeta_on_line_hasSum (v : ℝ) :
    HasSum (fun n : ℕ => Complex.exp
      (-contourPoint v * (Real.log ((n : ℝ) + 1) : ℂ)))
      (riemannZeta (contourPoint v)) := by
  have hv : 1 < (contourPoint v).re := by norm_num [contourPoint]
  have hS : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ (contourPoint v)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℂ) ^ (contourPoint v)) 1).mpr
        (Complex.summable_one_div_nat_cpow.mpr hv)
  simpa only [dirichlet_term_eq, zeta_eq_tsum_one_div_nat_add_one_cpow hv] using! hS.hasSum

private theorem pseries_summable :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-2 : ℝ)) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) 1).mpr
      (Real.summable_nat_rpow.mpr (by norm_num))

private theorem dirichlet_term_norm (v : ℝ) (n : ℕ) :
    ‖Complex.exp (-contourPoint v * (Real.log ((n : ℝ) + 1) : ℂ))‖ =
      ((n : ℝ) + 1) ^ (-2 : ℝ) := by
  rw [Complex.norm_exp, Real.rpow_def_of_pos (by positivity)]
  congr 1
  norm_num [contourPoint, Complex.mul_re]
  ring

private theorem mellin_integral_hasSum (T : ℝ) (hT : 0 < T) (w : ℂ) :
    HasSum (fun n : ℕ => ∫ v : ℝ,
      gammaFactor (contourPoint v) * gaussianKernel T w v *
        Complex.exp (-contourPoint v * (Real.log ((n : ℝ) + 1) : ℂ)))
      (∫ v : ℝ, gammaFactor (contourPoint v) * gaussianKernel T w v *
        riemannZeta (contourPoint v)) := by
  apply hasSum_integral_of_dominated_convergence
    (fun (n : ℕ) (v : ℝ) => ‖gammaFactor (contourPoint v) * gaussianKernel T w v‖ *
      ((n : ℝ) + 1) ^ (-2 : ℝ))
  · intro n
    have := gamma_factor_continuous_on_line
    unfold gaussianKernel contourPoint
    fun_prop
  · intro n
    filter_upwards with v
    rw [norm_mul, dirichlet_term_norm]
  · exact .of_forall fun v => pseries_summable.mul_left _
  · simp only [tsum_mul_left]
    exact (gamma_kernel_integrable T hT w).norm.mul_const _
  · exact .of_forall fun v => (zeta_on_line_hasSum v).mul_left _

theorem solution (t : ℝ) (ht : t < 0) (s : ℂ) :
    HasSum (fun n : ℕ => DeBruijnNewman.Dobner.mellinTerm t s n)
      (DeBruijnNewman.Dobner.xiT t (DeBruijnNewman.Dobner.J t s)) := by
  have hT : 0 < |t| := abs_pos.mpr ht.ne
  have hS := (mellin_integral_hasSum |t| hT (J t s)).mul_left
    (1 / (Real.sqrt (Real.pi * |t|) : ℂ))
  have hterm (n : ℕ) : mellinTerm t s n =
      (1 / (Real.sqrt (Real.pi * |t|) : ℂ)) *
        (∫ v : ℝ, gammaFactor (contourPoint v) * gaussianKernel |t| (J t s) v *
          Complex.exp (-contourPoint v * (Real.log ((n : ℝ) + 1) : ℂ))) := by
    simp only [mellinTerm, gaussianKernel, contourPoint, sub_eq_add_neg, Complex.exp_add,
      neg_mul, mul_assoc]
  have hxi (v : ℝ) : gammaFactor (contourPoint v) * gaussianKernel |t| (J t s) v *
      riemannZeta (contourPoint v) =
      xiT 0 (contourPoint v) * gaussianKernel |t| (J t s) v := by
    rw [xi_zero_eq_gamma_zeta (contourPoint v) (by norm_num [contourPoint])]
    ring
  simp_rw [hxi] at hS
  have hconv :
      (1 / (Real.sqrt (Real.pi * |t|) : ℂ)) *
        (∫ v : ℝ, xiT 0 (contourPoint v) * gaussianKernel |t| (J t s) v) =
        xiT t (J t s) := by
    simpa only [contourPoint, gaussianKernel] using gaussian_convolution t ht (J t s)
  rw [hconv] at hS
  simpa only [hterm] using! hS

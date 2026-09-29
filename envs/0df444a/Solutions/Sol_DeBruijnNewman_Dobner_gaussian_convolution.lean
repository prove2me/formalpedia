-- Prove2me | solution 1 for DeBruijnNewman.Dobner.gaussian_convolution
-- status  : ACCEPTED   (prove)
-- author  : @adobner
-- created : 2026-09-24T22:54:25.895783+00:00
-- url     : https://prove2.me/submissions/e28c1d64-53da-4271-8a77-5e36ed528ea0

import Definitions.Def_DeBruijnNewman_Dobner

open MeasureTheory Set Filter DeBruijnNewman DeBruijnNewman.Dobner
open scoped Topology

private noncomputable def phiMajorant (n : ℕ) : ℝ :=
  (2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 +
    3 * Real.pi * ((n : ℝ) + 1) ^ 2) * Real.exp (-((n : ℝ) + 1))

private theorem phi_majorant_summable : Summable phiMajorant := by
  have hs (k : ℕ) :
      Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k * Real.exp (-((n : ℝ) + 1))) := by
    have h : Summable (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-(n : ℝ))) := by
      simpa using Real.summable_pow_mul_exp_neg_nat_mul k (r := 1) zero_lt_one
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ k * Real.exp (-(n : ℝ))) 1).mpr h
  convert! ((hs 4).mul_left (2 * Real.pi ^ 2)).add ((hs 2).mul_left (3 * Real.pi)) using 1
  ext n
  dsimp [phiMajorant]
  ring

private theorem phi_gaussian_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ, 0 ≤ u →
      ‖Phi u‖ ≤ K * Real.exp (-u ^ 2 + 9 * u) := by
  have hnonneg (n : ℕ) : 0 ≤ phiMajorant n := by unfold phiMajorant; positivity
  refine ⟨∑' n, phiMajorant n, tsum_nonneg hnonneg, ?_⟩
  intro u hu
  have hb (n : ℕ) :
      ‖(2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u)
          - 3 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * u))
        * Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)))‖ ≤
      phiMajorant n * Real.exp (-u ^ 2 + 9 * u) := by
    let v : ℝ := (n : ℝ) + 1
    have hv : 1 ≤ v := le_add_of_nonneg_left (Nat.cast_nonneg n)
    have he4 : 1 ≤ Real.exp (4 * u) := Real.one_le_exp_iff.mpr (by positivity)
    have he4' : u ^ 2 ≤ Real.exp (4 * u) := by
      nlinarith [Real.quadratic_le_exp_of_nonneg (show 0 ≤ 4 * u by positivity)]
    have hbase : v + u ^ 2 ≤ Real.pi * v ^ 2 * Real.exp (4 * u) := by
      have hv' : v ≤ v ^ 2 * Real.exp (4 * u) :=
        (show v ≤ v ^ 2 by nlinarith).trans
          (le_mul_of_one_le_right (sq_nonneg v) he4)
      have hu' : u ^ 2 ≤ v ^ 2 * Real.exp (4 * u) :=
        he4'.trans (le_mul_of_one_le_left (Real.exp_nonneg _) (by nlinarith))
      have hp : 2 * (v ^ 2 * Real.exp (4 * u)) ≤
          Real.pi * (v ^ 2 * Real.exp (4 * u)) :=
        mul_le_mul_of_nonneg_right Real.two_le_pi (by positivity)
      nlinarith
    have he : Real.exp (-(Real.pi * v ^ 2 * Real.exp (4 * u))) ≤
        Real.exp (-v - u ^ 2) := Real.exp_le_exp.mpr (by linarith)
    have he5 : Real.exp (5 * u) ≤ Real.exp (9 * u) :=
      Real.exp_le_exp.mpr (by linarith)
    have hnorm :
        ‖2 * Real.pi ^ 2 * v ^ 4 * Real.exp (9 * u)
          - 3 * Real.pi * v ^ 2 * Real.exp (5 * u)‖ ≤
        2 * Real.pi ^ 2 * v ^ 4 * Real.exp (9 * u)
          + 3 * Real.pi * v ^ 2 * Real.exp (5 * u) := by
      calc
        _ ≤ ‖2 * Real.pi ^ 2 * v ^ 4 * Real.exp (9 * u)‖
          + ‖3 * Real.pi * v ^ 2 * Real.exp (5 * u)‖ := norm_sub_le _ _
        _ = _ := by
          rw [Real.norm_eq_abs, Real.norm_eq_abs]
          rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (2 * Real.pi ^ 2 * v ^ 4 * Real.exp (9 * u)
        + 3 * Real.pi * v ^ 2 * Real.exp (5 * u))
          * Real.exp (-(Real.pi * v ^ 2 * Real.exp (4 * u))) :=
        mul_le_mul_of_nonneg_right hnorm (Real.exp_nonneg _)
      _ ≤ (2 * Real.pi ^ 2 * v ^ 4 * Real.exp (9 * u)
        + 3 * Real.pi * v ^ 2 * Real.exp (9 * u)) * Real.exp (-v - u ^ 2) := by
        gcongr
      _ = phiMajorant n * Real.exp (-u ^ 2 + 9 * u) := by
        dsimp [phiMajorant, v]
        simp only [Real.exp_sub, Real.exp_add, Real.exp_neg]
        ring
  simpa only [Phi, tsum_mul_right] using
    tsum_of_norm_bounded
      (phi_majorant_summable.mul_right (Real.exp (-u ^ 2 + 9 * u))).hasSum hb

private theorem phi_measurable : Measurable Phi := by
  unfold Phi
  apply Measurable.tsum
  intro n
  fun_prop

private theorem real_quadratic_exp_integrable (t : ℝ) (ht : t < 0) (L : ℝ) :
    Integrable (fun u : ℝ => Real.exp (t * u ^ 2 + L * u)) := by
  have h := (integrable_cexp_quadratic' (b := (t : ℂ))
    (by simpa using ht) (L : ℂ) 0).norm
  simpa only [Complex.norm_exp, ← Complex.ofReal_pow, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, Complex.zero_re, add_zero] using h

private theorem phi_weight_integrable (L : ℝ) :
    IntegrableOn (fun u : ℝ => ‖Phi u‖ * Real.exp (L * u)) (Ioi 0) := by
  obtain ⟨K, hK, hphi⟩ := phi_gaussian_bound
  have hb := ((real_quadratic_exp_integrable (-1) (by norm_num) (9 + L)).const_mul K).restrict
    (s := Ioi (0 : ℝ))
  apply hb.mono'
    ((phi_measurable.norm.mul (by fun_prop)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  change ‖‖Phi u‖ * Real.exp (L * u)‖ ≤ K * Real.exp (-1 * u ^ 2 + (9 + L) * u)
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_nonneg _))]
  calc
    _ ≤ (K * Real.exp (-u ^ 2 + 9 * u)) * Real.exp (L * u) :=
      mul_le_mul_of_nonneg_right (hphi u hu.le) (Real.exp_nonneg _)
    _ = K * Real.exp (-1 * u ^ 2 + (9 + L) * u) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

private noncomputable def contourPoint (v : ℝ) : ℂ := 2 + (v : ℂ) * Complex.I

private noncomputable def gaussianKernel (T : ℝ) (w : ℂ) (v : ℝ) : ℂ :=
  Complex.exp ((w - contourPoint v) ^ 2 / (T : ℂ))

private theorem kernel_quadratic (T : ℝ) (w : ℂ) (v : ℝ) :
    (w - contourPoint v) ^ 2 / (T : ℂ) =
      (-1 / (T : ℂ)) * (v : ℂ) ^ 2 +
        (-2 * (w - 2) * Complex.I / (T : ℂ)) * (v : ℂ) +
        (w - 2) ^ 2 / (T : ℂ) := by
  dsimp [contourPoint]
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem kernel_integrable (T : ℝ) (hT : 0 < T) (w : ℂ) :
    Integrable (gaussianKernel T w) := by
  have hb : (-1 / (T : ℂ)).re < 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_neg, ← Complex.ofReal_div, Complex.ofReal_re]
    exact div_neg_of_neg_of_pos (by norm_num) hT
  unfold gaussianKernel
  simp only [kernel_quadratic]
  exact integrable_cexp_quadratic' hb (-2 * (w - 2) * Complex.I / (T : ℂ))
    ((w - 2) ^ 2 / (T : ℂ))

private theorem kernel_exp_quadratic (T : ℝ) (w : ℂ) (q v : ℝ) :
    gaussianKernel T w v * Complex.exp ((3 + 2 * (v : ℂ) * Complex.I) * (q : ℂ)) =
      Complex.exp ((-1 / (T : ℂ)) * (v : ℂ) ^ 2 +
        (-2 * (w - 2) * Complex.I / (T : ℂ) + 2 * Complex.I * (q : ℂ)) * (v : ℂ) +
        ((w - 2) ^ 2 / (T : ℂ) + 3 * (q : ℂ))) := by
  rw [gaussianKernel, ← Complex.exp_add, kernel_quadratic]
  congr 1
  ring

private theorem kernel_exp_integrable (T : ℝ) (hT : 0 < T) (w : ℂ) (q : ℝ) :
    Integrable (fun v : ℝ => gaussianKernel T w v *
      Complex.exp ((3 + 2 * (v : ℂ) * Complex.I) * (q : ℂ))) := by
  simp only [kernel_exp_quadratic]
  apply integrable_cexp_quadratic'
  rw [← Complex.ofReal_one, ← Complex.ofReal_neg, ← Complex.ofReal_div, Complex.ofReal_re]
  exact div_neg_of_neg_of_pos (by norm_num) hT

private theorem kernel_exp_integral (T : ℝ) (hT : 0 < T) (w : ℂ) (q : ℝ) :
    ∫ v : ℝ, gaussianKernel T w v *
      Complex.exp ((3 + 2 * (v : ℂ) * Complex.I) * (q : ℂ)) =
      (Real.sqrt (Real.pi * T) : ℂ) *
        Complex.exp (-(T : ℂ) * (q : ℂ) ^ 2 + (2 * w - 1) * (q : ℂ)) := by
  have hT0 : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  have hb : (-1 / (T : ℂ)).re < 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_neg, ← Complex.ofReal_div, Complex.ofReal_re]
    exact div_neg_of_neg_of_pos (by norm_num) hT
  simp only [kernel_exp_quadratic]
  rw [integral_cexp_quadratic hb]
  have hpi : (Real.pi : ℂ) / -(-1 / (T : ℂ)) = ((Real.pi * T : ℝ) : ℂ) := by
    push_cast
    field_simp
  have hp : (((Real.pi * T : ℝ) : ℂ) ^ (1 / 2 : ℂ)) =
      (Real.sqrt (Real.pi * T) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    norm_num
  rw [hpi, hp]
  congr 2
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem cosine_exp_split (w : ℂ) (u : ℝ) :
    Complex.cos (-Complex.I * (2 * w - 1) * (u : ℂ)) =
      (Complex.exp ((2 * w - 1) * (u : ℂ)) +
        Complex.exp ((2 * w - 1) * ((-u : ℝ) : ℂ))) / 2 := by
  have hp : (-Complex.I * (2 * w - 1) * (u : ℂ)) * Complex.I =
      (2 * w - 1) * (u : ℂ) := by
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hm : -(-Complex.I * (2 * w - 1) * (u : ℂ)) * Complex.I =
      (2 * w - 1) * ((-u : ℝ) : ℂ) := by
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [Complex.cos, hp, hm]

private theorem kernel_cos_integral (T : ℝ) (hT : 0 < T) (w : ℂ) (u : ℝ) :
    ∫ v : ℝ, gaussianKernel T w v *
      Complex.cos (-Complex.I * (2 * contourPoint v - 1) * (u : ℂ)) =
      (Real.sqrt (Real.pi * T) : ℂ) * (Real.exp (-T * u ^ 2) : ℂ) *
        Complex.cos (-Complex.I * (2 * w - 1) * (u : ℂ)) := by
  have hline (v : ℝ) : 2 * contourPoint v - 1 = 3 + 2 * (v : ℂ) * Complex.I := by
    unfold contourPoint
    ring
  simp only [cosine_exp_split]
  simp only [hline, ← mul_div_assoc, mul_add]
  rw [integral_div,
    integral_add (kernel_exp_integrable T hT w u) (kernel_exp_integrable T hT w (-u)),
    kernel_exp_integral T hT w, kernel_exp_integral T hT w]
  push_cast
  simp only [neg_sq, Complex.exp_add]
  ring

private theorem contour_cos_norm_bound (v u : ℝ) (hu : 0 ≤ u) :
    ‖Complex.cos (-Complex.I * (2 * contourPoint v - 1) * (u : ℂ))‖ ≤
      Real.exp (3 * u) := by
  have hp : ‖Complex.exp ((2 * contourPoint v - 1) * (u : ℂ))‖ =
      Real.exp (3 * u) := by
    rw [Complex.norm_exp]
    congr 1
    norm_num [contourPoint, Complex.mul_re]
  have hm : ‖Complex.exp ((2 * contourPoint v - 1) * ((-u : ℝ) : ℂ))‖ ≤
      Real.exp (3 * u) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp [contourPoint, Complex.mul_re]
    linarith
  rw [cosine_exp_split, norm_div, Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have hh := norm_add_le
    (Complex.exp ((2 * contourPoint v - 1) * (u : ℂ)))
    (Complex.exp ((2 * contourPoint v - 1) * ((-u : ℝ) : ℂ)))
  rw [hp] at hh
  linarith

private theorem kernel_heat_product_integrable (T : ℝ) (hT : 0 < T) (w : ℂ) :
    Integrable (fun p : ℝ × ℝ =>
      gaussianKernel T w p.1 * (Phi p.2 : ℂ) *
        Complex.cos (-Complex.I * (2 * contourPoint p.1 - 1) * (p.2 : ℂ)))
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hb := (kernel_integrable T hT w).norm.mul_prod (phi_weight_integrable 3)
  apply hb.mono'
  · have := phi_measurable
    unfold gaussianKernel contourPoint
    fun_prop
  · have hu : ∀ᵐ p : ℝ × ℝ ∂volume.prod (volume.restrict (Ioi (0 : ℝ))), 0 ≤ p.2 :=
      (Measure.ae_prod_iff_ae_ae (measurableSet_le measurable_const measurable_snd)).mpr
        (.of_forall fun _ =>
          (ae_restrict_mem measurableSet_Ioi).mono fun _ h => h.le)
    filter_upwards [hu] with p hp
    rw [norm_mul, norm_mul, Complex.norm_real]
    calc
      _ ≤ (‖gaussianKernel T w p.1‖ * ‖Phi p.2‖) * Real.exp (3 * p.2) :=
        mul_le_mul_of_nonneg_left (contour_cos_norm_bound p.1 p.2 hp) (by positivity)
      _ = _ := mul_assoc _ _ _

private theorem heat_gaussian_convolution (t : ℝ) (ht : t < 0) (w : ℂ) :
    (1 / (Real.sqrt (Real.pi * |t|) : ℂ)) *
      (∫ v : ℝ, xiT 0 (contourPoint v) * gaussianKernel |t| w v) = xiT t w := by
  have hT : 0 < |t| := abs_pos.mpr ht.ne
  have ht' : -|t| = t := by rw [abs_of_neg ht, neg_neg]
  have hsqrt : (Real.sqrt (Real.pi * |t|) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (mul_pos Real.pi_pos hT)).ne'
  have hswap := integral_integral_swap
    (f := fun v u : ℝ => gaussianKernel |t| w v * (Phi u : ℂ) *
      Complex.cos (-Complex.I * (2 * contourPoint v - 1) * (u : ℂ)))
    (kernel_heat_product_integrable |t| hT w)
  have h0 (v : ℝ) :
      gaussianKernel |t| w v * H 0 (-Complex.I * (2 * contourPoint v - 1)) =
        ∫ u : ℝ in Ioi 0, gaussianKernel |t| w v * (Phi u : ℂ) *
          Complex.cos (-Complex.I * (2 * contourPoint v - 1) * (u : ℂ)) := by
    simp only [H, zero_mul, Real.exp_zero, one_mul, ← integral_const_mul, mul_assoc]
  have hin (u : ℝ) :
      (∫ v : ℝ, gaussianKernel |t| w v * (Phi u : ℂ) *
        Complex.cos (-Complex.I * (2 * contourPoint v - 1) * (u : ℂ))) =
      (Real.sqrt (Real.pi * |t|) : ℂ) *
        (((Real.exp (t * u ^ 2) * Phi u : ℝ) : ℂ) *
          Complex.cos (-Complex.I * (2 * w - 1) * (u : ℂ))) := by
    simp_rw [mul_comm (gaussianKernel |t| w _) (Phi u : ℂ), mul_assoc]
    have hcos := kernel_cos_integral |t| hT w u
    simp only [mul_assoc] at hcos
    rw [integral_const_mul, hcos, ht']
    push_cast
    ring
  have hGH :
      (∫ v : ℝ, gaussianKernel |t| w v * H 0 (-Complex.I * (2 * contourPoint v - 1))) =
      (Real.sqrt (Real.pi * |t|) : ℂ) * H t (-Complex.I * (2 * w - 1)) := by
    simp_rw [h0]
    rw [hswap]
    simp_rw [hin]
    rw [integral_const_mul]
    rfl
  unfold xiT
  simp_rw [show ∀ v : ℝ, 8 * H 0 (-Complex.I * (2 * contourPoint v - 1)) *
      gaussianKernel |t| w v =
      8 * (gaussianKernel |t| w v * H 0 (-Complex.I * (2 * contourPoint v - 1))) by
        intro v; ring]
  rw [integral_const_mul, hGH]
  field_simp

theorem solution (t : ℝ) (ht : t < 0) (s : ℂ) :
    (1 / (Real.sqrt (Real.pi * |t|) : ℂ)) *
      (∫ v : ℝ, DeBruijnNewman.Dobner.xiT 0 (2 + (v : ℂ) * Complex.I) *
        Complex.exp ((s - (2 + (v : ℂ) * Complex.I)) ^ 2 / ((|t| : ℝ) : ℂ))) =
      DeBruijnNewman.Dobner.xiT t s := by
  exact heat_gaussian_convolution t ht s

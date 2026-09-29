-- Prove2me | solution 1 for DeBruijnNewman.H_entire_negative
-- status  : ACCEPTED   (prove)
-- author  : @adobner
-- created : 2026-09-24T22:33:30.974992+00:00
-- url     : https://prove2.me/submissions/af1297a0-8f24-4fd8-9466-b4933603b812

import Definitions.Def_DeBruijnNewman_core

open MeasureTheory Set Filter Metric
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

private theorem phi_majorant_nonneg (n : ℕ) : 0 ≤ phiMajorant n := by
  unfold phiMajorant
  positivity

private theorem phi_exp_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ, 0 ≤ u →
      ‖DeBruijnNewman.Phi u‖ ≤ K * Real.exp (9 * u) := by
  refine ⟨∑' n, phiMajorant n, tsum_nonneg phi_majorant_nonneg, ?_⟩
  intro u hu
  have hb (n : ℕ) :
      ‖(2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u)
          - 3 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * u))
        * Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)))‖ ≤
      phiMajorant n * Real.exp (9 * u) := by
    let v : ℝ := (n : ℝ) + 1
    have hv : 1 ≤ v := le_add_of_nonneg_left (Nat.cast_nonneg n)
    have he4 : 1 ≤ Real.exp (4 * u) := Real.one_le_exp_iff.mpr (by positivity)
    have hbase : v ≤ Real.pi * v ^ 2 * Real.exp (4 * u) := by
      calc
        v ≤ v ^ 2 := by nlinarith
        _ ≤ Real.pi * v ^ 2 :=
          le_mul_of_one_le_left (sq_nonneg v) (by linarith [Real.two_le_pi])
        _ ≤ Real.pi * v ^ 2 * Real.exp (4 * u) :=
          le_mul_of_one_le_right (by positivity) he4
    have he : Real.exp (-(Real.pi * v ^ 2 * Real.exp (4 * u))) ≤ Real.exp (-v) :=
      Real.exp_le_exp.mpr (neg_le_neg hbase)
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
        + 3 * Real.pi * v ^ 2 * Real.exp (9 * u)) * Real.exp (-v) := by
        gcongr
      _ = phiMajorant n * Real.exp (9 * u) := by dsimp [phiMajorant, v]; ring
  simpa only [DeBruijnNewman.Phi, tsum_mul_right] using
    tsum_of_norm_bounded (phi_majorant_summable.mul_right (Real.exp (9 * u))).hasSum hb

private theorem phi_measurable : Measurable DeBruijnNewman.Phi := by
  unfold DeBruijnNewman.Phi
  apply Measurable.tsum
  intro n
  fun_prop

private theorem complex_trig_norm_bound (z : ℂ) :
    ‖Complex.cos z‖ ≤ Real.exp ‖z‖ ∧ ‖Complex.sin z‖ ≤ Real.exp ‖z‖ := by
  have hp : ‖Complex.exp (z * Complex.I)‖ ≤ Real.exp ‖z‖ := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using Complex.re_le_norm (z * Complex.I)
  have hm : ‖Complex.exp (-z * Complex.I)‖ ≤ Real.exp ‖z‖ := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using Complex.re_le_norm (-z * Complex.I)
  constructor
  · rw [Complex.cos, norm_div, Complex.norm_ofNat]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have := norm_add_le (Complex.exp (z * Complex.I)) (Complex.exp (-z * Complex.I))
    linarith
  · rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have := norm_sub_le (Complex.exp (-z * Complex.I)) (Complex.exp (z * Complex.I))
    linarith

private theorem real_quadratic_exp_integrable (t : ℝ) (ht : t < 0) (L : ℝ) :
    Integrable (fun u : ℝ => Real.exp (t * u ^ 2 + L * u)) := by
  have h := (integrable_cexp_quadratic' (b := (t : ℂ))
    (by simpa using ht) (L : ℂ) 0).norm
  simpa only [Complex.norm_exp, ← Complex.ofReal_pow, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, Complex.zero_re, add_zero] using h

private noncomputable def heatIntegrand (t : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  ((Real.exp (t * u ^ 2) * DeBruijnNewman.Phi u : ℝ) : ℂ) * Complex.cos (z * (u : ℂ))

private noncomputable def heatDeriv (t : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  ((Real.exp (t * u ^ 2) * DeBruijnNewman.Phi u : ℝ) : ℂ) *
    (-Complex.sin (z * (u : ℂ)) * (u : ℂ))

private theorem heat_integrand_measurable (t : ℝ) (z : ℂ) :
    Measurable (heatIntegrand t z) := by
  unfold heatIntegrand
  have := phi_measurable
  fun_prop

private theorem heat_deriv_measurable (t : ℝ) (z : ℂ) :
    Measurable (heatDeriv t z) := by
  unfold heatDeriv
  have := phi_measurable
  fun_prop

private theorem heat_integrand_hasDerivAt (t : ℝ) (u : ℝ) (z : ℂ) :
    HasDerivAt (fun w => heatIntegrand t w u) (heatDeriv t z u) z := by
  simpa only [heatIntegrand, heatDeriv, mul_one, one_mul, Function.comp_def, id_eq] using!
    ((Complex.hasDerivAt_cos (z * (u : ℂ))).comp z
      ((hasDerivAt_id z).mul_const (u : ℂ))).const_mul
        ((Real.exp (t * u ^ 2) * DeBruijnNewman.Phi u : ℝ) : ℂ)

private theorem heat_integrand_norm_bound (t : ℝ) (z : ℂ) (u K : ℝ)
    (hu : 0 ≤ u) (hK : 0 ≤ K) (hphi : ‖DeBruijnNewman.Phi u‖ ≤ K * Real.exp (9 * u)) :
    ‖heatIntegrand t z u‖ ≤ K * Real.exp (t * u ^ 2 + (9 + ‖z‖) * u) := by
  unfold heatIntegrand
  rw [norm_mul, Complex.norm_real, norm_mul, Real.norm_eq_abs (Real.exp _),
    abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (Real.exp (t * u ^ 2) * (K * Real.exp (9 * u))) *
        Real.exp ‖z * (u : ℂ)‖ := by
      gcongr
      exact (complex_trig_norm_bound _).1
    _ = _ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
      rw [show t * u ^ 2 + (9 + ‖z‖) * u =
        (t * u ^ 2 + 9 * u) + ‖z‖ * u by ring]
      simp only [Real.exp_add]
      ring

private theorem heat_deriv_norm_bound (t : ℝ) (z : ℂ) (u K : ℝ)
    (hu : 0 ≤ u) (hK : 0 ≤ K) (hphi : ‖DeBruijnNewman.Phi u‖ ≤ K * Real.exp (9 * u)) :
    ‖heatDeriv t z u‖ ≤ K * Real.exp (t * u ^ 2 + (10 + ‖z‖) * u) := by
  unfold heatDeriv
  rw [norm_mul, Complex.norm_real, norm_mul, Real.norm_eq_abs (Real.exp _),
    abs_of_pos (Real.exp_pos _), norm_mul, norm_neg, Complex.norm_real,
    Real.norm_eq_abs u, abs_of_nonneg hu]
  have hu_exp : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  calc
    _ ≤ (Real.exp (t * u ^ 2) * (K * Real.exp (9 * u))) *
        (Real.exp ‖z * (u : ℂ)‖ * Real.exp u) := by
      gcongr
      exact (complex_trig_norm_bound _).2
    _ = _ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
      rw [show t * u ^ 2 + (10 + ‖z‖) * u =
        (t * u ^ 2 + 9 * u) + (‖z‖ * u + u) by ring]
      simp only [Real.exp_add]
      ring

theorem solution (t : ℝ) (ht : t < 0) :
    Differentiable ℂ (DeBruijnNewman.H t) := by
  obtain ⟨K, hK, hphi⟩ := phi_exp_bound
  intro z₀
  let bound : ℝ → ℝ := fun u => K * Real.exp (t * u ^ 2 + (11 + ‖z₀‖) * u)
  have hb_int : Integrable bound (volume.restrict (Ioi (0 : ℝ))) :=
    ((real_quadratic_exp_integrable t ht (11 + ‖z₀‖)).const_mul K).restrict
  have hF_int : Integrable (heatIntegrand t z₀) (volume.restrict (Ioi (0 : ℝ))) := by
    apply hb_int.mono' (heat_integrand_measurable t z₀).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := hu.le
    apply (heat_integrand_norm_bound t z₀ u K hu.le hK (hphi u hu.le)).trans
    dsimp [bound]
    gcongr
    linarith
  have hF_meas : ∀ᶠ z in 𝓝 z₀,
      AEStronglyMeasurable (heatIntegrand t z) (volume.restrict (Ioi (0 : ℝ))) :=
    .of_forall fun z => (heat_integrand_measurable t z).aestronglyMeasurable
  have hFd_meas : AEStronglyMeasurable (heatDeriv t z₀) (volume.restrict (Ioi (0 : ℝ))) :=
    (heat_deriv_measurable t z₀).aestronglyMeasurable
  have hb : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), ∀ z ∈ ball z₀ 1,
      ‖heatDeriv t z u‖ ≤ bound u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu z hz
    have hu0 : 0 ≤ u := hu.le
    have hz_norm : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have h := norm_le_norm_sub_add z z₀
      have hz' : ‖z - z₀‖ < 1 := mem_ball_iff_norm.mp hz
      linarith
    apply (heat_deriv_norm_bound t z u K hu.le hK (hphi u hu.le)).trans
    dsimp [bound]
    apply mul_le_mul_of_nonneg_left _ hK
    apply Real.exp_le_exp.mpr
    have hlinear : 10 + ‖z‖ ≤ 11 + ‖z₀‖ := by linarith
    linarith [mul_le_mul_of_nonneg_right hlinear hu0]
  have hd : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), ∀ z ∈ ball z₀ 1,
      HasDerivAt (fun w => heatIntegrand t w u) (heatDeriv t z u) z :=
    .of_forall fun u z _ => heat_integrand_hasDerivAt t u z
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (ball_mem_nhds z₀ zero_lt_one) hF_meas hF_int hFd_meas hb hb_int hd
  exact h.2.differentiableAt

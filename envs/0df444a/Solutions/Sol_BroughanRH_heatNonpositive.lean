-- Prove2me | solution 1 for BroughanRH.heatNonpositive
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T18:43:07.245014+00:00
-- url     : https://prove2.me/submissions/202e385c-9ca5-465e-ba54-7dd4e619d19c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DeBruijnNewman_core
import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_DeBruijnNewman_Dobner_xi_zero_eq_gamma_zeta
import Theorems.Thm_DeBruijnNewman_debruijn_newman_constant_nonneg


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

private theorem phi_gauss_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ, 0 ≤ u →
      ‖DeBruijnNewman.Phi u‖ ≤ (K * Real.exp (-16 * u ^ 2)) * Real.exp (9 * u) := by
  refine ⟨∑' n, phiMajorant n, tsum_nonneg phi_majorant_nonneg, ?_⟩
  intro u hu
  have hb (n : ℕ) :
      ‖(2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u)
          - 3 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * u))
        * Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)))‖ ≤
      phiMajorant n * (Real.exp (-16 * u ^ 2) * Real.exp (9 * u)) := by
    let v : ℝ := (n : ℝ) + 1
    have hv : 1 ≤ v := le_add_of_nonneg_left (Nat.cast_nonneg n)
    have he4 : 1 ≤ Real.exp (4 * u) := Real.one_le_exp_iff.mpr (by positivity)
    have hq : 1 + 4 * u + (4 * u) ^ 2 / 2 ≤ Real.exp (4 * u) :=
      Real.quadratic_le_exp_of_nonneg (by positivity)
    have hpi : 3 ≤ Real.pi := le_of_lt Real.pi_gt_three
    have hbase : v + 16 * u ^ 2 ≤ Real.pi * v ^ 2 * Real.exp (4 * u) := by
      have hv2 : 1 ≤ v ^ 2 := by nlinarith
      have h1 : v ≤ v ^ 2 * Real.exp (4 * u) := by nlinarith
      have h2 : 2 * Real.exp (4 * u) ≤ (Real.pi - 1) * v ^ 2 * Real.exp (4 * u) := by
        have : 2 ≤ (Real.pi - 1) * v ^ 2 := by nlinarith
        nlinarith
      nlinarith
    have he : Real.exp (-(Real.pi * v ^ 2 * Real.exp (4 * u))) ≤
        Real.exp (-v) * Real.exp (-16 * u ^ 2) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
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
        + 3 * Real.pi * v ^ 2 * Real.exp (9 * u)) * (Real.exp (-v) * Real.exp (-16 * u ^ 2)) := by
        gcongr
      _ = phiMajorant n * (Real.exp (-16 * u ^ 2) * Real.exp (9 * u)) := by
        dsimp [phiMajorant, v]; ring
  have := tsum_of_norm_bounded
    (phi_majorant_summable.mul_right (Real.exp (-16 * u ^ 2) * Real.exp (9 * u))).hasSum hb
  simp only [tsum_mul_right] at this
  simpa only [DeBruijnNewman.Phi, mul_assoc] using this

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

private theorem H0_entire : Differentiable ℂ (DeBruijnNewman.H 0) := by
  obtain ⟨K, hK, hphi⟩ := phi_gauss_bound
  intro z₀
  let bound : ℝ → ℝ := fun u => K * Real.exp (-16 * u ^ 2 + (11 + ‖z₀‖) * u)
  have hb_int : Integrable bound (volume.restrict (Ioi (0 : ℝ))) :=
    ((real_quadratic_exp_integrable (-16) (by norm_num) (11 + ‖z₀‖)).const_mul K).restrict
  have hK' : ∀ u : ℝ, 0 ≤ K * Real.exp (-16 * u ^ 2) := fun u => by positivity
  have hrw : ∀ (u c : ℝ), K * Real.exp (-16 * u ^ 2) * Real.exp (0 * u ^ 2 + c * u) =
      K * Real.exp (-16 * u ^ 2 + c * u) := by
    intro u c; rw [Real.exp_add (-16 * u ^ 2)]; simp; ring
  have hF_int : Integrable (heatIntegrand 0 z₀) (volume.restrict (Ioi (0 : ℝ))) := by
    apply hb_int.mono' (heat_integrand_measurable 0 z₀).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := hu.le
    apply (heat_integrand_norm_bound 0 z₀ u _ hu.le (hK' u) (hphi u hu.le)).trans
    rw [hrw]
    dsimp [bound]
    gcongr
    linarith
  have hF_meas : ∀ᶠ z in 𝓝 z₀,
      AEStronglyMeasurable (heatIntegrand 0 z) (volume.restrict (Ioi (0 : ℝ))) :=
    .of_forall fun z => (heat_integrand_measurable 0 z).aestronglyMeasurable
  have hFd_meas : AEStronglyMeasurable (heatDeriv 0 z₀) (volume.restrict (Ioi (0 : ℝ))) :=
    (heat_deriv_measurable 0 z₀).aestronglyMeasurable
  have hb : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), ∀ z ∈ ball z₀ 1,
      ‖heatDeriv 0 z u‖ ≤ bound u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu z hz
    have hu0 : 0 ≤ u := hu.le
    have hz_norm : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have h := norm_le_norm_sub_add z z₀
      have hz' : ‖z - z₀‖ < 1 := mem_ball_iff_norm.mp hz
      linarith
    apply (heat_deriv_norm_bound 0 z u _ hu.le (hK' u) (hphi u hu.le)).trans
    rw [hrw]
    dsimp [bound]
    apply mul_le_mul_of_nonneg_left _ hK
    apply Real.exp_le_exp.mpr
    have hlinear : 10 + ‖z‖ ≤ 11 + ‖z₀‖ := by linarith
    linarith [mul_le_mul_of_nonneg_right hlinear hu0]
  have hd : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), ∀ z ∈ ball z₀ 1,
      HasDerivAt (fun w => heatIntegrand 0 w u) (heatDeriv 0 z u) z :=
    .of_forall fun u z _ => heat_integrand_hasDerivAt 0 u z
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (ball_mem_nhds z₀ zero_lt_one) hF_meas hF_int hFd_meas hb hb_int hd
  exact h.2.differentiableAt

/-- `Λ(s) ≠ 0` for `Re s ≥ 1`, `s ≠ 1`. -/
private lemma completed_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) (hs1 : s ≠ 1) :
    completedRiemannZeta s ≠ 0 := by
  have hpos : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := by rintro rfl; simp at hpos
  have hζ := riemannZeta_ne_zero_of_one_le_re hs
  rw [riemannZeta_def_of_ne_zero hs0] at hζ
  intro h
  rw [h, zero_div] at hζ
  exact hζ rfl

private noncomputable def xiM (s : ℂ) : ℂ := (1 + s * (s-1) * completedRiemannZeta₀ s) / 2

/-- Under RH, zeros of `xiM` lie on the critical line. -/
private lemma xiM_zero_re {s : ℂ} (hx' : xiM s = 0) : s.re = 1/2 := by
  have hx : 1 + s * (s-1) * completedRiemannZeta₀ s = 0 := by
    unfold xiM at hx'; linear_combination 2 * hx'
  have hs0 : s ≠ 0 := by rintro h; rw [h] at hx; simp at hx
  have hs1 : s ≠ 1 := by rintro h; rw [h] at hx; simp at hx
  have h1s : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hΛ : completedRiemannZeta s = 0 := by
    rw [completedRiemannZeta_eq]
    have hss : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    field_simp
    linear_combination (-1 : ℂ) * hx
  rcases le_or_gt 1 s.re with h | h
  · exact absurd hΛ (completed_ne_zero_of_one_le_re h hs1)
  rcases le_or_gt s.re 0 with h' | h'
  · have : 1 ≤ (1 - s).re := by simp; linarith
    refine absurd ?_ (completed_ne_zero_of_one_le_re this ?_)
    · rw [completedRiemannZeta_one_sub]; exact hΛ
    · intro h2; apply hs0; linear_combination -h2
  have hζ : riemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs0, hΛ, zero_div]
  apply riemann_hypothesis s hζ
  · rintro ⟨n, hn⟩
    rw [hn] at h'
    simp at h'
    have : (0:ℝ) ≤ n := n.cast_nonneg
    linarith
  · exact hs1

private lemma xiM_eq_of_re_gt_one {s : ℂ} (hs : 1 < s.re) :
    DeBruijnNewman.Dobner.xiT 0 s = xiM s := by
  rw [DeBruijnNewman.Dobner.xi_zero_eq_gamma_zeta s hs]
  have hpos : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := by rintro rfl; simp at hpos
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  have h1s : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hss : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hG : DeBruijnNewman.Dobner.gammaFactor s = s * (s - 1) / 2 * Complex.Gammaℝ s := by
    unfold DeBruijnNewman.Dobner.gammaFactor
    rw [Complex.Gammaℝ_def, Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.pi_ne_zero),
      ← Complex.ofReal_log Real.pi_pos.le]
    rw [show ((Real.log Real.pi : ℝ) : ℂ) * (-s / 2) = -(s / 2) * ((Real.log Real.pi : ℝ) : ℂ) by ring]
    ring
  rw [hG, riemannZeta_def_of_ne_zero hs0, xiM, completedRiemannZeta_eq]
  have hGne := Complex.Gammaℝ_ne_zero_of_re_pos hpos
  field_simp
  ring

private lemma xiT0_eq : DeBruijnNewman.Dobner.xiT 0 = xiM := by
  have hF : Differentiable ℂ (DeBruijnNewman.Dobner.xiT 0) := by
    intro s
    unfold DeBruijnNewman.Dobner.xiT
    have := H0_entire
    fun_prop
  have hG : Differentiable ℂ xiM := by
    intro s
    unfold xiM
    have := differentiable_completedZeta₀
    fun_prop
  apply AnalyticOnNhd.eq_of_eventuallyEq (z₀ := (2 : ℂ))
    (hF.differentiableOn.analyticOnNhd isOpen_univ)
    (hG.differentiableOn.analyticOnNhd isOpen_univ)
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds (by simp : (1:ℝ) < (2:ℂ).re)] with s hs
  exact xiM_eq_of_re_gt_one hs

private theorem heat_time_zero : DeBruijnNewman.HasOnlyRealZeros 0 := by
  intro z hz
  set s : ℂ := (1 + Complex.I * z) / 2 with hsdef
  have hzs : -Complex.I * (2 * s - 1) = z := by
    rw [hsdef]; ring_nf; rw [Complex.I_sq]; ring
  have hx : xiM s = 0 := by
    rw [← xiT0_eq]
    unfold DeBruijnNewman.Dobner.xiT
    rw [hzs, hz, mul_zero]
  have := xiM_zero_re hx
  rw [hsdef] at this
  simp at this
  linarith
theorem solution :
    DeBruijnNewman.Lambda ≤ 0 := by
  unfold DeBruijnNewman.Lambda
  exact csInf_le ⟨0, fun t ht => DeBruijnNewman.debruijn_newman_constant_nonneg.2 t ht⟩
    heat_time_zero

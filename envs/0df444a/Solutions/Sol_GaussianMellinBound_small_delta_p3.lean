-- Prove2me | solution 1 for GaussianMellinBound.small_delta_p3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T03:33:07.895993+00:00
-- url     : https://prove2.me/submissions/da5480f9-fb4b-4f1d-a057-2eaf1a98d60c

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic


open Real Complex MeasureTheory Filter Set
open scoped Topology

noncomputable section
namespace GaussSmallBridge

/-! ### Part 1: Imaginary-axis Taylor bounds for `Complex.exp (I * θ)` -/

lemma hasDerivAt_ofReal_C (u : ℝ) : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 u := by
  simpa using (hasDerivAt_id u).ofReal_comp

lemma hasDerivAt_cexp_neg_I (u : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp (-(Complex.I * (x : ℂ))))
      (-Complex.I * Complex.exp (-(Complex.I * (u : ℂ)))) u := by
  simpa [mul_comm] using (((hasDerivAt_ofReal_C u).const_mul Complex.I).neg.cexp)

lemma norm_cexp_neg_I (u : ℝ) :
    ‖Complex.exp (-(Complex.I * (u : ℂ)))‖ = 1 := by
  have : -(Complex.I * (u : ℂ)) = ((-u : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma norm_cexp_I (u : ℝ) :
    ‖Complex.exp (Complex.I * (u : ℂ))‖ = 1 := by
  have : Complex.I * (u : ℂ) = (u : ℂ) * Complex.I := mul_comm _ _
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma norm_cexp_I_sub_T0 (θ : ℝ) :
    ‖Complex.exp (Complex.I * (θ : ℂ)) - 1‖ ≤ |θ| := by
  simpa [Real.norm_eq_abs] using norm_exp_I_mul_ofReal_sub_one_le (x := θ)

private lemma norm_cexp_I_sub_T1_nonneg {θ : ℝ} (hθ : 0 ≤ θ) :
    ‖Complex.exp (Complex.I * (θ : ℂ)) - (1 + Complex.I * (θ : ℂ))‖ ≤ θ ^ 2 / 2 := by
  let g : ℝ → ℂ := fun u => 1 - Complex.exp (-(Complex.I * (u : ℂ))) * (1 + Complex.I * (u : ℂ))
  let g' : ℝ → ℂ := fun u => -(u : ℂ) * Complex.exp (-(Complex.I * (u : ℂ)))
  have hnorm_eq : ‖Complex.exp (Complex.I * (θ : ℂ)) - (1 + Complex.I * (θ : ℂ))‖ = ‖g θ‖ := by
    have hmul : Complex.exp (-(Complex.I * (θ : ℂ))) *
        (Complex.exp (Complex.I * (θ : ℂ)) - (1 + Complex.I * (θ : ℂ))) = g θ := by
      dsimp [g]
      rw [mul_sub, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    rw [← hmul, norm_mul, norm_cexp_neg_I, one_mul]
  rw [hnorm_eq]
  have hderiv : ∀ u : ℝ, HasDerivAt g (g' u) u := by
    intro u
    have h1 := hasDerivAt_cexp_neg_I u
    have h2 : HasDerivAt (fun x : ℝ => (1 : ℂ) + Complex.I * (x : ℂ)) Complex.I u := by
      simpa using ((hasDerivAt_ofReal_C u).const_mul Complex.I).const_add (1 : ℂ)
    have hprod := (h1.fun_mul h2).const_sub (1 : ℂ)
    refine hprod.congr_deriv ?_
    dsimp [g']
    calc
      -(-Complex.I * cexp (-(Complex.I * ↑u)) * (1 + Complex.I * ↑u) +
          cexp (-(Complex.I * ↑u)) * Complex.I)
        = Complex.I ^ 2 * ↑u * cexp (-(Complex.I * ↑u)) := by ring
      _ = -↑u * cexp (-(Complex.I * ↑u)) := by rw [Complex.I_sq]; ring
  have hg0 : g 0 = 0 := by simp [g]
  have hint_g' : IntervalIntegrable g' volume 0 θ :=
    (Continuous.intervalIntegrable (by dsimp [g']; fun_prop) 0 θ)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u) hint_g'
  rw [hg0, sub_zero] at hftc
  rw [← hftc]
  have hbound : ∀ u ∈ Ioc 0 θ, ‖g' u‖ ≤ u := by
    intro u hu
    dsimp [g']
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu.1,
      norm_cexp_neg_I, mul_one]
  calc
    ‖∫ u in (0)..θ, g' u‖ ≤ ∫ u in (0)..θ, u :=
      intervalIntegral.norm_integral_le_of_norm_le hθ (Eventually.of_forall fun u hu => hbound u hu)
        (continuous_id.intervalIntegrable 0 θ)
    _ = θ ^ 2 / 2 := by simp [integral_id]

lemma norm_cexp_I_sub_T1 (θ : ℝ) :
    ‖Complex.exp (Complex.I * (θ : ℂ)) - (1 + Complex.I * (θ : ℂ))‖ ≤ θ ^ 2 / 2 := by
  rcases le_total 0 θ with hθ | hθ
  · exact norm_cexp_I_sub_T1_nonneg hθ
  · have hneg : 0 ≤ -θ := neg_nonneg.mpr hθ
    have h1 := norm_cexp_I_sub_T1_nonneg hneg
    have hconj : starRingEnd ℂ (Complex.exp (Complex.I * (θ : ℂ)) - (1 + Complex.I * (θ : ℂ))) =
        Complex.exp (Complex.I * ((-θ : ℝ) : ℂ)) - (1 + Complex.I * ((-θ : ℝ) : ℂ)) := by
      rw [map_sub, ← Complex.exp_conj]
      simp [mul_comm Complex.I]
    rw [← RCLike.norm_conj (K := ℂ), hconj]
    simpa [sq] using h1

private lemma norm_cexp_I_sub_T2_nonneg {θ : ℝ} (hθ : 0 ≤ θ) :
    ‖Complex.exp (Complex.I * (θ : ℂ)) -
      (1 + Complex.I * (θ : ℂ) - (1 / 2 : ℂ) * ((θ : ℂ) * (θ : ℂ)))‖ ≤ θ ^ 3 / 6 := by
  let p : ℝ → ℂ := fun u => 1 + Complex.I * (u : ℂ) - (1 / 2 : ℂ) * ((u : ℂ) * (u : ℂ))
  let g : ℝ → ℂ := fun u => 1 - Complex.exp (-(Complex.I * (u : ℂ))) * p u
  let g' : ℝ → ℂ := fun u => -(Complex.I / 2) * ((u : ℂ) * (u : ℂ)) * Complex.exp (-(Complex.I * (u : ℂ)))
  have hnorm_eq : ‖Complex.exp (Complex.I * (θ : ℂ)) - p θ‖ = ‖g θ‖ := by
    have hmul : Complex.exp (-(Complex.I * (θ : ℂ))) * (Complex.exp (Complex.I * (θ : ℂ)) - p θ) = g θ := by
      dsimp [g]
      rw [mul_sub, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    rw [← hmul, norm_mul, norm_cexp_neg_I, one_mul]
  rw [hnorm_eq]
  have hderiv : ∀ u : ℝ, HasDerivAt g (g' u) u := by
    intro u
    have h1 := hasDerivAt_cexp_neg_I u
    have hu_sq : HasDerivAt (fun x : ℝ => (x : ℂ) * (x : ℂ)) (2 * (u : ℂ)) u := by
      simpa [two_mul] using (hasDerivAt_ofReal_C u).fun_mul (hasDerivAt_ofReal_C u)
    have hp : HasDerivAt p (Complex.I - (u : ℂ)) u := by
      have ha := ((hasDerivAt_ofReal_C u).const_mul Complex.I).const_add (1 : ℂ)
      have hb := hu_sq.const_mul (1 / 2 : ℂ)
      refine (ha.sub hb).congr_deriv (by ring)
    refine ((h1.fun_mul hp).const_sub (1 : ℂ)).congr_deriv ?_
    dsimp [g', p]
    calc
      -(-Complex.I * cexp (-(Complex.I * ↑u)) * (1 + Complex.I * ↑u - 1 / 2 * (↑u * ↑u)) +
          cexp (-(Complex.I * ↑u)) * (Complex.I - ↑u))
        = (Complex.I ^ 2 + 1) * ↑u * cexp (-(Complex.I * ↑u)) -
            (Complex.I / 2) * (↑u * ↑u) * cexp (-(Complex.I * ↑u)) := by ring
      _ = -(Complex.I / 2) * (↑u * ↑u) * cexp (-(Complex.I * ↑u)) := by rw [Complex.I_sq]; ring
  have hg0 : g 0 = 0 := by simp [g, p]
  have hint_g' : IntervalIntegrable g' volume 0 θ :=
    (Continuous.intervalIntegrable (by dsimp [g']; fun_prop) 0 θ)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u) hint_g'
  rw [hg0, sub_zero] at hftc
  rw [← hftc]
  have hbound : ∀ u ∈ Ioc 0 θ, ‖g' u‖ ≤ (1 / 2 : ℝ) * u ^ 2 := by
    intro u _
    dsimp [g']
    rw [norm_mul, norm_mul, norm_neg, norm_div, Complex.norm_I, Complex.norm_ofNat,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cexp_neg_I]
    have : |u| * |u| = u ^ 2 := by rw [← abs_mul, mul_self_eq_mul_self_iff.mpr (Or.inl rfl), abs_of_nonneg (mul_self_nonneg u)]; ring
    linarith
  calc
    ‖∫ u in (0)..θ, g' u‖ ≤ ∫ u in (0)..θ, (1 / 2 : ℝ) * u ^ 2 :=
      intervalIntegral.norm_integral_le_of_norm_le hθ (Eventually.of_forall fun u hu => hbound u hu)
        (Continuous.intervalIntegrable (by fun_prop) 0 θ)
    _ = (1 / 2 : ℝ) * (∫ u in (0)..θ, u ^ 2) := intervalIntegral.integral_const_mul _ _
    _ = θ ^ 3 / 6 := by rw [integral_pow]; ring

lemma norm_cexp_I_sub_T2 (θ : ℝ) :
    ‖Complex.exp (Complex.I * (θ : ℂ)) -
      (1 + Complex.I * (θ : ℂ) - (1 / 2 : ℂ) * ((θ : ℂ) * (θ : ℂ)))‖ ≤ |θ| ^ 3 / 6 := by
  rcases le_total 0 θ with hθ | hθ
  · rw [abs_of_nonneg hθ]
    exact norm_cexp_I_sub_T2_nonneg hθ
  · have hneg : 0 ≤ -θ := neg_nonneg.mpr hθ
    rw [abs_of_nonpos hθ]
    have h1 := norm_cexp_I_sub_T2_nonneg hneg
    have hconj : starRingEnd ℂ (Complex.exp (Complex.I * (θ : ℂ)) -
        (1 + Complex.I * (θ : ℂ) - (1 / 2 : ℂ) * ((θ : ℂ) * (θ : ℂ)))) =
        Complex.exp (Complex.I * ((-θ : ℝ) : ℂ)) -
          (1 + Complex.I * ((-θ : ℝ) : ℂ) - (1 / 2 : ℂ) * (((-θ : ℝ) : ℂ) * ((-θ : ℝ) : ℂ))) := by
      rw [map_sub, ← Complex.exp_conj]
      apply Complex.ext <;> simp
    rw [← RCLike.norm_conj (K := ℂ), hconj]
    exact h1

end GaussSmallBridge
end


open Real Complex MeasureTheory Filter Set
open scoped Topology

noncomputable section
namespace GaussSmallBridge

/-! ### Part 2: Mellin split at `R = 3` and log-power integrals on `Ioc 0 1` -/

lemma x_mul_exp_neg_le_half {x : ℝ} (hx : 0 ≤ x) :
    x * Real.exp (-x) ≤ 1 / 2 := by
  have hexp_pos : 0 < Real.exp x := Real.exp_pos x
  have h1 : 2 * x ≤ Real.exp x := by
    have hq := Real.quadratic_le_exp_of_nonneg hx
    have hsq : 0 ≤ (x - 1) ^ 2 := sq_nonneg (x - 1)
    linarith
  have h2 : x * Real.exp (-x) = x / Real.exp x := by
    rw [Real.exp_neg, div_eq_mul_inv]
  rw [h2, div_le_iff₀ hexp_pos]
  linarith

lemma tail3_int_and_bound (δ t : ℝ) :
    let s : ℂ := (1 / 2 : ℂ) + (t : ℝ) * Complex.I
    let f : ℝ → ℂ := fun u =>
      (u : ℂ) ^ (s - 1) * ((Real.exp (-u ^ 2 / 2) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ)))
    IntegrableOn f (Ioi 3) ∧ ‖∫ u : ℝ in Ioi 3, f u‖ ≤ Real.sqrt 3 * (1 / 801 : ℝ) := by
  intro s f
  let dom : ℝ → ℝ := fun u => (1 / (3 * Real.sqrt 3)) * (u * Real.exp (-u ^ 2 / 2))
  have hprim : ∀ u : ℝ, HasDerivAt (fun x : ℝ => -Real.exp (-x ^ 2 / 2))
      (u * Real.exp (-u ^ 2 / 2)) u := by
    intro u
    have h1 : HasDerivAt (fun x : ℝ => -x ^ 2 / 2) (-u) u := by
      have := (hasDerivAt_pow 2 u).neg.div_const 2
      exact this.congr_deriv (by ring)
    exact (h1.exp.neg).congr_deriv (by ring)
  have htend_top : Tendsto (fun x : ℝ => -Real.exp (-x ^ 2 / 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => x ^ 2 / 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).atTop_div_const (by norm_num)
    have h2 : Tendsto (fun x : ℝ => Real.exp (-x ^ 2 / 2)) atTop (𝓝 0) :=
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).congr fun x => by
        dsimp [Function.comp]; ring_nf
    simpa using h2.neg
  have hcont3 : ContinuousWithinAt (fun x : ℝ => -Real.exp (-x ^ 2 / 2)) (Ici 3) 3 :=
    (Continuous.continuousAt (by fun_prop)).continuousWithinAt
  have h_u_int : IntegrableOn (fun u : ℝ => u * Real.exp (-u ^ 2 / 2)) (Ioi 3) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (Real.exp (-9 / 2)) 3
      (fun b => Continuous.integrableOn_Ioc (by fun_prop)) tendsto_id ?_
    filter_upwards [Ici_mem_atTop (3 : ℝ)] with b hb
    dsimp only [id]
    have heq : ∫ x in (3)..b, ‖x * Real.exp (-x ^ 2 / 2)‖ =
        ∫ x in (3)..b, x * Real.exp (-x ^ 2 / 2) := by
      rw [intervalIntegral.integral_of_le hb, intervalIntegral.integral_of_le hb]
      refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
      exact Real.norm_of_nonneg (mul_nonneg (by linarith [hx.1]) (Real.exp_nonneg _))
    rw [heq]
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hprim x)
      (Continuous.intervalIntegrable (by fun_prop) 3 b)
    rw [hftc]
    have h3 : -(Real.exp (-(3 : ℝ) ^ 2 / 2)) = -Real.exp (-9 / 2) := by norm_num
    linarith [Real.exp_pos (-b ^ 2 / 2), h3]
  have h_u_val : ∫ u : ℝ in Ioi 3, u * Real.exp (-u ^ 2 / 2) = Real.exp (-9 / 2) := by
    have hftc := integral_Ioi_of_hasDerivAt_of_tendsto hcont3 (fun u _ => hprim u) h_u_int htend_top
    norm_num at hftc ⊢
    linarith
  have hdom_int : IntegrableOn dom (Ioi 3) := h_u_int.const_mul _
  have hpt : ∀ᵐ u ∂volume.restrict (Ioi 3), ‖f u‖ ≤ dom u := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    have hu3 : (3 : ℝ) < u := hu
    have hu0 : 0 < u := by linarith
    dsimp [f, dom]
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_nonneg _)]
    have hcexp : ‖Complex.exp (2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ))‖ = 1 := by
      have : 2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ) =
          ((2 * Real.pi * (δ * u) : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    have hs1 : (s - 1).re = -(1 / 2 : ℝ) := by simp [s]; norm_num
    rw [hcexp, mul_one, hs1]
    have hrpow : u ^ (-(1 / 2 : ℝ)) ≤ (1 / (3 * Real.sqrt 3)) * u := by
      have h1 : u ^ (-(1 / 2 : ℝ)) = (Real.sqrt u)⁻¹ := by
        rw [Real.sqrt_eq_rpow, Real.rpow_neg hu0.le]
      rw [h1]
      have hsq3 : Real.sqrt 3 ≤ Real.sqrt u := Real.sqrt_le_sqrt hu3.le
      have hprod : 3 * Real.sqrt 3 ≤ u * Real.sqrt u :=
        mul_le_mul hu3.le hsq3 (Real.sqrt_nonneg _) (by linarith)
      have hsu_pos : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
      rw [inv_le_iff_one_le_mul₀' hsu_pos]
      calc
        (1 : ℝ) = (1 / (3 * Real.sqrt 3)) * (3 * Real.sqrt 3) := by field_simp
        _ ≤ (1 / (3 * Real.sqrt 3)) * (u * Real.sqrt u) :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = Real.sqrt u * (1 / (3 * Real.sqrt 3) * u) := by ring
    calc
      u ^ (-(1 / 2 : ℝ)) * Real.exp (-u ^ 2 / 2)
        ≤ ((1 / (3 * Real.sqrt 3)) * u) * Real.exp (-u ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right hrpow (Real.exp_nonneg _)
      _ = (1 / (3 * Real.sqrt 3)) * (u * Real.exp (-u ^ 2 / 2)) := by ring
  have hf_meas : AEStronglyMeasurable f (volume.restrict (Ioi 3)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul ?_ (Continuous.continuousOn (by fun_prop))
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_trans (by norm_num) hu
    exact (continuousAt_ofReal_cpow_const _ _ (Or.inr hu0.ne')).continuousWithinAt
  have hf_int : IntegrableOn f (Ioi 3) := hdom_int.mono' hf_meas hpt
  refine ⟨hf_int, ?_⟩
  have hnorm_le : ‖∫ u in Ioi 3, f u‖ ≤ (1 / (3 * Real.sqrt 3)) * Real.exp (-9 / 2) := by
    calc
      ‖∫ u in Ioi 3, f u‖ ≤ ∫ u in Ioi 3, dom u :=
        le_trans (norm_integral_le_integral_norm _) (integral_mono_ae hf_int.norm hdom_int hpt)
      _ = (1 / (3 * Real.sqrt 3)) * ∫ u in Ioi 3, u * Real.exp (-u ^ 2 / 2) :=
        integral_const_mul _ _
      _ = (1 / (3 * Real.sqrt 3)) * Real.exp (-9 / 2) := by rw [h_u_val]
  have halg : (1 / (3 * Real.sqrt 3)) * Real.exp (-9 / 2) = Real.sqrt 3 * (Real.exp (-9 / 2) / 9) := by
    have hs3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hne : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    field_simp [hne]
    rw [hs3]; ring
  rw [halg] at hnorm_le
  have hexp_bound : Real.exp (-9 / 2) / 9 ≤ 1 / 801 := by
    have he_lo : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have hsq : (89 : ℝ) ^ 2 < (Real.exp (9 / 2)) ^ 2 := by
      have : (Real.exp (9 / 2)) ^ 2 = (Real.exp 1) ^ 9 := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; congr 1; norm_num
      rw [this]
      calc
        (89 : ℝ) ^ 2 < (2.718 : ℝ) ^ 9 := by norm_num
        _ < (Real.exp 1) ^ 9 := pow_lt_pow_left₀ he_lo (by norm_num) (by norm_num)
    have h89 : (89 : ℝ) < Real.exp (9 / 2) := by
      by_contra hle; push Not at hle
      have := pow_le_pow_left₀ (Real.exp_nonneg _) hle 2
      linarith
    have hinv : Real.exp (-9 / 2) ≤ 1 / 89 := by
      rw [show (-9 / 2 : ℝ) = -(9 / 2) by norm_num, Real.exp_neg, one_div]
      exact inv_anti₀ (by norm_num) h89.le
    linarith
  exact le_trans hnorm_le (mul_le_mul_of_nonneg_left hexp_bound (Real.sqrt_nonneg _))

/-! ### Real and Complex Log-Power Integrals on `Ioc 0 1` via `AECover` -/

lemma tendsto_rpow_mul_log_pow_nhdsGT_zero {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Tendsto (fun w : ℝ => w ^ a * (Real.log w) ^ k) (𝓝[>] 0) (𝓝 0) := by
  have hlog : Tendsto (fun w : ℝ => a * (-Real.log w)) (𝓝[>] 0) atTop :=
    Tendsto.const_mul_atTop ha (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)
  have hbase := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp hlog
  have hmul := hbase.const_mul ((-1 / a) ^ k)
  rw [mul_zero] at hmul
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hw0 : 0 < w := hw
  dsimp [Function.comp]
  have hexp : Real.exp (-(a * -Real.log w)) = w ^ a := by
    have : -(a * -Real.log w) = Real.log w * a := by ring
    rw [this, ← Real.rpow_def_of_pos hw0]
  rw [hexp, mul_pow]
  have ha_ne : a ≠ 0 := ha.ne'
  calc
    (-1 / a) ^ k * (a ^ k * (-Real.log w) ^ k * w ^ a)
      = w ^ a * ((-1 / a * a) ^ k * (-Real.log w) ^ k) := by
          rw [mul_pow]; ring
    _ = w ^ a * ((-1 : ℝ) * -Real.log w) ^ k := by
          have : -1 / a * a = -1 := by field_simp [ha_ne]
          rw [this, mul_pow]
    _ = w ^ a * (Real.log w) ^ k := by ring_nf

private lemma real_improper_Ioc01 {F f : ℝ → ℝ}
    (hderiv : ∀ w > 0, HasDerivAt F (f w) w)
    (hnn : ∀ w ∈ Ioc (0 : ℝ) 1, 0 ≤ f w)
    (hcont : ContinuousOn f (Ioc 0 1))
    (ht0 : Tendsto F (𝓝[>] 0) (𝓝 0)) :
    IntegrableOn f (Ioc 0 1) ∧ ∫ w in Ioc 0 1, f w = F 1 := by
  let a : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  have ha_pos : ∀ n, 0 < a n := fun n => by dsimp [a]; positivity
  have ha_le1 : ∀ n, a n ≤ 1 := fun n => by
    dsimp [a]
    exact div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by positivity)
  have ha_tend_gt : Tendsto a atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall ha_pos⟩
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    exact (tendsto_inv_atTop_zero.comp h1).congr fun n => by simp [a, Function.comp, one_div]
  have ha_tend : Tendsto a atTop (𝓝 0) := ha_tend_gt.mono_right nhdsWithin_le_nhds
  have hφ : AECover (volume.restrict (Ioc 0 1)) atTop (fun n => Ioc (a n) 1) :=
    aecover_Ioc_of_Ioc ha_tend tendsto_const_nhds
  have hsub : ∀ n, Ioc (a n) 1 ⊆ Ioc 0 1 := fun n => Ioc_subset_Ioc_left (ha_pos n).le
  have hsub_cc : ∀ n, Icc (a n) 1 ⊆ Ioc 0 1 :=
    fun n _ hx => ⟨lt_of_lt_of_le (ha_pos n) hx.1, hx.2⟩
  have hfi : ∀ n, IntegrableOn f (Ioc (a n) 1) (volume.restrict (Ioc 0 1)) := by
    intro n
    rw [IntegrableOn, Measure.restrict_restrict_of_subset (hsub n)]
    exact (hcont.mono (hsub_cc n)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hval : ∀ n, ∫ w in Ioc (a n) 1, f w ∂(volume.restrict (Ioc 0 1)) = F 1 - F (a n) := by
    intro n
    rw [Measure.restrict_restrict_of_subset (hsub n), ← intervalIntegral.integral_of_le (ha_le1 n)]
    have hint_iv : IntervalIntegrable f volume (a n) 1 := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le (ha_le1 n)]
      exact (hcont.mono (hsub_cc n)).integrableOn_Icc
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hderiv x (lt_of_lt_of_le (ha_pos n) (by rw [uIcc_of_le (ha_le1 n)] at hx; exact hx.1)))
      hint_iv
  have htend_int : Tendsto (fun n => ∫ w in Ioc (a n) 1, f w ∂(volume.restrict (Ioc 0 1))) atTop (𝓝 (F 1)) := by
    simp_rw [hval]
    simpa using tendsto_const_nhds.sub (ht0.comp ha_tend_gt)
  have hnng_ae : 0 ≤ᵐ[volume.restrict (Ioc 0 1)] f := by
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall hnn
  have hf_int : IntegrableOn f (Ioc 0 1) :=
    hφ.integrable_of_integral_tendsto_of_nonneg_ae (F 1) hfi hnng_ae htend_int
  exact ⟨hf_int, hφ.integral_eq_of_tendsto (F 1) hf_int htend_int⟩

private lemma complex_improper_Ioc01 {F f : ℝ → ℂ} {g_dom : ℝ → ℝ}
    (hderiv : ∀ w > 0, HasDerivAt F (f w) w)
    (hg_int : IntegrableOn g_dom (Ioc 0 1))
    (hdom : ∀ w ∈ Ioc (0 : ℝ) 1, ‖f w‖ ≤ g_dom w)
    (hcont : ContinuousOn f (Ioc 0 1))
    (ht0 : Tendsto F (𝓝[>] 0) (𝓝 0)) :
    IntegrableOn f (Ioc 0 1) ∧ ∫ w in Ioc 0 1, f w = F 1 := by
  let a : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  have ha_pos : ∀ n, 0 < a n := fun n => by dsimp [a]; positivity
  have ha_le1 : ∀ n, a n ≤ 1 := fun n => by
    dsimp [a]
    exact div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by positivity)
  have ha_tend_gt : Tendsto a atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall ha_pos⟩
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    exact (tendsto_inv_atTop_zero.comp h1).congr fun n => by simp [a, Function.comp, one_div]
  have ha_tend : Tendsto a atTop (𝓝 0) := ha_tend_gt.mono_right nhdsWithin_le_nhds
  have hφ : AECover (volume.restrict (Ioc 0 1)) atTop (fun n => Ioc (a n) 1) :=
    aecover_Ioc_of_Ioc ha_tend tendsto_const_nhds
  have hsub : ∀ n, Ioc (a n) 1 ⊆ Ioc 0 1 := fun n => Ioc_subset_Ioc_left (ha_pos n).le
  have hsub_cc : ∀ n, Icc (a n) 1 ⊆ Ioc 0 1 :=
    fun n _ hx => ⟨lt_of_lt_of_le (ha_pos n) hx.1, hx.2⟩
  have hf_int : IntegrableOn f (Ioc 0 1) := by
    refine hg_int.mono' (hcont.aestronglyMeasurable measurableSet_Ioc) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall hdom
  have hval : ∀ n, ∫ w in Ioc (a n) 1, f w ∂(volume.restrict (Ioc 0 1)) = F 1 - F (a n) := by
    intro n
    rw [Measure.restrict_restrict_of_subset (hsub n), ← intervalIntegral.integral_of_le (ha_le1 n)]
    have hint_iv : IntervalIntegrable f volume (a n) 1 := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le (ha_le1 n)]
      exact (hcont.mono (hsub_cc n)).integrableOn_Icc
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hderiv x (lt_of_lt_of_le (ha_pos n) (by rw [uIcc_of_le (ha_le1 n)] at hx; exact hx.1)))
      hint_iv
  have htend_int : Tendsto (fun n => ∫ w in Ioc (a n) 1, f w ∂(volume.restrict (Ioc 0 1))) atTop (𝓝 (F 1)) := by
    simp_rw [hval]
    simpa using tendsto_const_nhds.sub (ht0.comp ha_tend_gt)
  exact ⟨hf_int, hφ.integral_eq_of_tendsto (F 1) hf_int htend_int⟩

lemma real_integral_rpow_neg_log_pow_Ioc {a : ℝ} (ha : 0 < a) :
    (IntegrableOn (fun w : ℝ => w ^ (a - 1)) (Ioc 0 1) ∧ ∫ w : ℝ in Ioc 0 1, w ^ (a - 1) = 1 / a) ∧
    (IntegrableOn (fun w : ℝ => w ^ (a - 1) * (-Real.log w)) (Ioc 0 1) ∧
      ∫ w : ℝ in Ioc 0 1, w ^ (a - 1) * (-Real.log w) = 1 / a ^ 2) ∧
    (IntegrableOn (fun w : ℝ => w ^ (a - 1) * (Real.log w) ^ 2) (Ioc 0 1) ∧
      ∫ w : ℝ in Ioc 0 1, w ^ (a - 1) * (Real.log w) ^ 2 = 2 / a ^ 3) ∧
    (IntegrableOn (fun w : ℝ => w ^ (a - 1) * (-Real.log w) ^ 3) (Ioc 0 1) ∧
      ∫ w : ℝ in Ioc 0 1, w ^ (a - 1) * (-Real.log w) ^ 3 = 6 / a ^ 4) := by
  have ha_ne : a ≠ 0 := ha.ne'
  have hd_rpow : ∀ w > (0 : ℝ), HasDerivAt (fun x : ℝ => x ^ a) (a * w ^ (a - 1)) w :=
    fun w hw => Real.hasDerivAt_rpow_const (Or.inl hw.ne')
  have hd_log : ∀ w > (0 : ℝ), HasDerivAt Real.log w⁻¹ w :=
    fun w hw => Real.hasDerivAt_log hw.ne'
  have hmul_id : ∀ w > (0 : ℝ), w ^ a * w⁻¹ = w ^ (a - 1) := fun w hw => by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hw]; ring_nf
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- k = 0
    let F0 : ℝ → ℝ := fun w => (1 / a) * w ^ a
    have h0 := real_improper_Ioc01 (F := F0) (f := fun w => w ^ (a - 1))
      (fun w hw => ((hd_rpow w hw).const_mul (1 / a)).congr_deriv (by field_simp [ha_ne]))
      (fun w hw => Real.rpow_nonneg hw.1.le _)
      (ContinuousOn.rpow_const continuousOn_id fun w hw => Or.inl hw.1.ne')
      (by simpa [F0] using (tendsto_rpow_mul_log_pow_nhdsGT_zero ha 0).const_mul (1 / a))
    exact ⟨h0.1, by simpa [F0] using h0.2⟩
  · -- k = 1
    let F1 : ℝ → ℝ := fun w => (1 / a ^ 2) * (w ^ a * (1 - a * Real.log w))
    have hd1 : ∀ w > (0 : ℝ), HasDerivAt F1 (w ^ (a - 1) * (-Real.log w)) w := by
      intro w hw
      have hp := (hd_rpow w hw).mul (((hd_log w hw).const_mul a).const_sub 1)
      refine (hp.const_mul (1 / a ^ 2)).congr_deriv ?_
      have hm := hmul_id w hw
      calc
        1 / a ^ 2 * (a * w ^ (a - 1) * (1 - a * Real.log w) + w ^ a * -(a * w⁻¹))
          = 1 / a ^ 2 * (a * w ^ (a - 1) * (1 - a * Real.log w) - a * (w ^ a * w⁻¹)) := by ring
        _ = 1 / a ^ 2 * (a * w ^ (a - 1) * (1 - a * Real.log w) - a * w ^ (a - 1)) := by rw [hm]
        _ = w ^ (a - 1) * (-Real.log w) := by field_simp [ha_ne]; ring
    have ht1 : Tendsto F1 (𝓝[>] 0) (𝓝 0) := by
      have t0 := tendsto_rpow_mul_log_pow_nhdsGT_zero ha 0
      have t1 := (tendsto_rpow_mul_log_pow_nhdsGT_zero ha 1).const_mul a
      have hcomb := (t0.sub t1).const_mul (1 / a ^ 2)
      simp only [mul_zero, sub_zero] at hcomb
      exact hcomb.congr fun w => by dsimp [F1]; ring
    have h1 := real_improper_Ioc01 hd1
      (fun w hw => mul_nonneg (Real.rpow_nonneg hw.1.le _)
        (neg_nonneg.mpr (Real.log_nonpos hw.1.le hw.2)))
      ((ContinuousOn.rpow_const continuousOn_id fun w hw => Or.inl hw.1.ne').mul
        (ContinuousOn.neg (Real.continuousOn_log.mono fun w hw => hw.1.ne')))
      ht1
    exact ⟨h1.1, by simpa [F1] using h1.2⟩
  · -- k = 2
    let F2 : ℝ → ℝ := fun w => (1 / a ^ 3) * (w ^ a * (2 - 2 * a * Real.log w + a ^ 2 * (Real.log w) ^ 2))
    have hd2 : ∀ w > (0 : ℝ), HasDerivAt F2 (w ^ (a - 1) * (Real.log w) ^ 2) w := by
      intro w hw
      have hlog2_mul : HasDerivAt (fun x => Real.log x * Real.log x) (2 * Real.log w * w⁻¹) w :=
        ((hd_log w hw).fun_mul (hd_log w hw)).congr_deriv (by ring)
      have hlog2 : HasDerivAt (fun x => (Real.log x) ^ 2) (2 * Real.log w * w⁻¹) w :=
        hlog2_mul.congr_of_eventuallyEq (Eventually.of_forall fun x => sq (Real.log x))
      have hpoly : HasDerivAt (fun x => 2 - 2 * a * Real.log x + a ^ 2 * (Real.log x) ^ 2)
          (-(2 * a * w⁻¹) + a ^ 2 * (2 * Real.log w * w⁻¹)) w :=
        (((hd_log w hw).const_mul (2 * a)).const_sub 2).add (hlog2.const_mul (a ^ 2))
      refine (((hd_rpow w hw).mul hpoly).const_mul (1 / a ^ 3)).congr_deriv ?_
      have hm := hmul_id w hw
      calc
        1 / a ^ 3 * (a * w ^ (a - 1) * (2 - 2 * a * Real.log w + a ^ 2 * Real.log w ^ 2) +
            w ^ a * (-(2 * a * w⁻¹) + a ^ 2 * (2 * Real.log w * w⁻¹)))
          = 1 / a ^ 3 * (a * w ^ (a - 1) * (2 - 2 * a * Real.log w + a ^ 2 * Real.log w ^ 2) +
              (-2 * a + 2 * a ^ 2 * Real.log w) * (w ^ a * w⁻¹)) := by ring
        _ = 1 / a ^ 3 * (a * w ^ (a - 1) * (2 - 2 * a * Real.log w + a ^ 2 * Real.log w ^ 2) +
              (-2 * a + 2 * a ^ 2 * Real.log w) * w ^ (a - 1)) := by rw [hm]
        _ = w ^ (a - 1) * Real.log w ^ 2 := by field_simp [ha_ne]; ring
    have ht2 : Tendsto F2 (𝓝[>] 0) (𝓝 0) := by
      have t0 := (tendsto_rpow_mul_log_pow_nhdsGT_zero ha 0).const_mul 2
      have t1 := (tendsto_rpow_mul_log_pow_nhdsGT_zero ha 1).const_mul (2 * a)
      have t2 := (tendsto_rpow_mul_log_pow_nhdsGT_zero ha 2).const_mul (a ^ 2)
      have hcomb := (((t0.sub t1).add t2).const_mul (1 / a ^ 3))
      simp only [mul_zero, sub_zero, add_zero] at hcomb
      exact hcomb.congr fun w => by dsimp [F2]; ring
    have h2 := real_improper_Ioc01 hd2
      (fun w hw => mul_nonneg (Real.rpow_nonneg hw.1.le _) (sq_nonneg _))
      ((ContinuousOn.rpow_const continuousOn_id fun w hw => Or.inl hw.1.ne').mul
        ((Real.continuousOn_log.mono fun w hw => hw.1.ne').pow 2))
      ht2
    exact ⟨h2.1, by rw [h2.2]; dsimp [F2]; simp; ring⟩
  · -- k = 3
    let F3 : ℝ → ℝ := fun w =>
      (1 / a ^ 4) * (w ^ a * (6 - 6 * a * Real.log w + 3 * a ^ 2 * (Real.log w) ^ 2 - a ^ 3 * (Real.log w) ^ 3))
    have hd3 : ∀ w > (0 : ℝ), HasDerivAt F3 (w ^ (a - 1) * (-Real.log w) ^ 3) w := by
      intro w hw
      have hlog2_mul : HasDerivAt (fun x => Real.log x * Real.log x) (2 * Real.log w * w⁻¹) w :=
        ((hd_log w hw).fun_mul (hd_log w hw)).congr_deriv (by ring)
      have hlog2 : HasDerivAt (fun x => (Real.log x) ^ 2) (2 * Real.log w * w⁻¹) w :=
        hlog2_mul.congr_of_eventuallyEq (Eventually.of_forall fun x => sq (Real.log x))
      have hlog3_mul : HasDerivAt (fun x => (Real.log x) ^ 2 * Real.log x) (3 * (Real.log w) ^ 2 * w⁻¹) w :=
        (hlog2.fun_mul (hd_log w hw)).congr_deriv (by ring)
      have hlog3 : HasDerivAt (fun x => (Real.log x) ^ 3) (3 * (Real.log w) ^ 2 * w⁻¹) w :=
        hlog3_mul.congr_of_eventuallyEq (Eventually.of_forall fun x => pow_succ (Real.log x) 2)
      have hpoly : HasDerivAt
          (fun x => 6 - 6 * a * Real.log x + 3 * a ^ 2 * (Real.log x) ^ 2 - a ^ 3 * (Real.log x) ^ 3)
          (-(6 * a * w⁻¹) + 3 * a ^ 2 * (2 * Real.log w * w⁻¹) - a ^ 3 * (3 * (Real.log w) ^ 2 * w⁻¹)) w :=
        ((((hd_log w hw).const_mul (6 * a)).const_sub 6).add (hlog2.const_mul (3 * a ^ 2))).sub
          (hlog3.const_mul (a ^ 3))
      refine (((hd_rpow w hw).mul hpoly).const_mul (1 / a ^ 4)).congr_deriv ?_
      have hm := hmul_id w hw
      calc
        1 / a ^ 4 * (a * w ^ (a - 1) *
              (6 - 6 * a * Real.log w + 3 * a ^ 2 * Real.log w ^ 2 - a ^ 3 * Real.log w ^ 3) +
            w ^ a * (-(6 * a * w⁻¹) + 3 * a ^ 2 * (2 * Real.log w * w⁻¹) -
              a ^ 3 * (3 * Real.log w ^ 2 * w⁻¹)))
          = 1 / a ^ 4 * (a * w ^ (a - 1) *
              (6 - 6 * a * Real.log w + 3 * a ^ 2 * Real.log w ^ 2 - a ^ 3 * Real.log w ^ 3) +
              (-6 * a + 6 * a ^ 2 * Real.log w - 3 * a ^ 3 * Real.log w ^ 2) * (w ^ a * w⁻¹)) := by ring
        _ = 1 / a ^ 4 * (a * w ^ (a - 1) *
              (6 - 6 * a * Real.log w + 3 * a ^ 2 * Real.log w ^ 2 - a ^ 3 * Real.log w ^ 3) +
              (-6 * a + 6 * a ^ 2 * Real.log w - 3 * a ^ 3 * Real.log w ^ 2) * w ^ (a - 1)) := by rw [hm]
        _ = w ^ (a - 1) * (-Real.log w) ^ 3 := by field_simp [ha_ne]; ring
    have ht3 : Tendsto F3 (𝓝[>] 0) (𝓝 0) := by
      have t0 := (tendsto_rpow_mul_log_pow_nhdsGT_zero ha 0).const_mul 6
      have t1 := (tendsto_rpow_mul_log_pow_nhdsGT_zero ha 1).const_mul (6 * a)
      have t2 := (tendsto_rpow_mul_log_pow_nhdsGT_zero ha 2).const_mul (3 * a ^ 2)
      have t3 := (tendsto_rpow_mul_log_pow_nhdsGT_zero ha 3).const_mul (a ^ 3)
      have hcomb := ((((t0.sub t1).add t2).sub t3).const_mul (1 / a ^ 4))
      simp only [mul_zero, sub_zero, add_zero] at hcomb
      exact hcomb.congr fun w => by dsimp [F3]; ring
    have h3 := real_improper_Ioc01 hd3
      (fun w hw => mul_nonneg (Real.rpow_nonneg hw.1.le _)
        (pow_nonneg (neg_nonneg.mpr (Real.log_nonpos hw.1.le hw.2)) 3))
      ((ContinuousOn.rpow_const continuousOn_id fun w hw => Or.inl hw.1.ne').mul
        ((ContinuousOn.neg (Real.continuousOn_log.mono fun w hw => hw.1.ne')).pow 3))
      ht3
    exact ⟨h3.1, by rw [h3.2]; dsimp [F3]; simp; ring⟩

lemma complex_integral_cpow_log_Ioc {z : ℂ} (hz : 0 < z.re) :
    (IntegrableOn (fun w : ℝ => (w : ℂ) ^ (z - 1)) (Ioc 0 1) ∧
      ∫ w : ℝ in Ioc 0 1, (w : ℂ) ^ (z - 1) = 1 / z) ∧
    (IntegrableOn (fun w : ℝ => (Real.log w : ℂ) * (w : ℂ) ^ (z - 1)) (Ioc 0 1) ∧
      ∫ w : ℝ in Ioc 0 1, ((Real.log w : ℂ) * (w : ℂ) ^ (z - 1)) = -1 / z ^ 2) ∧
    (IntegrableOn (fun w : ℝ => ((Real.log w : ℂ) * (Real.log w : ℂ)) * (w : ℂ) ^ (z - 1)) (Ioc 0 1) ∧
      ∫ w : ℝ in Ioc 0 1, (((Real.log w : ℂ) * (Real.log w : ℂ)) * (w : ℂ) ^ (z - 1)) = 2 / z ^ 3) := by
  have hz_ne : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  obtain ⟨⟨hdom0, _⟩, ⟨hdom1, _⟩, ⟨hdom2, _⟩, _⟩ := real_integral_rpow_neg_log_pow_Ioc hz
  have hd_cpow : ∀ w > (0 : ℝ), HasDerivAt (fun x : ℝ => (x : ℂ) ^ z) (z * (w : ℂ) ^ (z - 1)) w :=
    fun w hw => hasDerivAt_ofReal_cpow_const hw.ne' hz_ne
  have hd_clog : ∀ w > (0 : ℝ), HasDerivAt (fun x : ℝ => (Real.log x : ℂ)) ((w⁻¹ : ℝ) : ℂ) w :=
    fun w hw => by simpa using (Real.hasDerivAt_log hw.ne').ofReal_comp
  have hmul_cid : ∀ w > (0 : ℝ), (w : ℂ) ^ z * ((w⁻¹ : ℝ) : ℂ) = (w : ℂ) ^ (z - 1) := by
    intro w hw
    have hw_ne : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
    have hinv : ((w⁻¹ : ℝ) : ℂ) = (w : ℂ) ^ (-1 : ℂ) := by
      rw [Complex.ofReal_inv, Complex.cpow_neg_one]
    rw [hinv, ← Complex.cpow_add _ _ hw_ne]; ring_nf
  have ht_cpow_log : ∀ k : ℕ, Tendsto (fun w : ℝ => (w : ℂ) ^ z * (Real.log w : ℂ) ^ k) (𝓝[>] 0) (𝓝 0) := by
    intro k
    refine squeeze_zero_norm' (a := fun w : ℝ => |w ^ z.re * (Real.log w) ^ k|) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with w hw
      have hw0 : 0 < w := hw
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hw0, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hw0 _), abs_pow]
    · simpa using (tendsto_rpow_mul_log_pow_nhdsGT_zero hz k).abs
  refine ⟨?_, ?_, ?_⟩
  · -- k = 0
    let G0 : ℝ → ℂ := fun w => (1 / z) * (w : ℂ) ^ z
    have h0 := complex_improper_Ioc01 (F := G0) (f := fun w => (w : ℂ) ^ (z - 1))
      (g_dom := fun w => w ^ (z.re - 1))
      (fun w hw => ((hd_cpow w hw).const_mul (1 / z)).congr_deriv (by field_simp [hz_ne]))
      hdom0
      (fun w hw => by rw [Complex.norm_cpow_eq_rpow_re_of_pos hw.1]; simp)
      (fun w hw => (continuousAt_ofReal_cpow_const _ _ (Or.inr hw.1.ne')).continuousWithinAt)
      (by simpa [G0] using (ht_cpow_log 0).const_mul (1 / z))
    exact ⟨h0.1, by simpa [G0] using h0.2⟩
  · -- k = 1
    let G1 : ℝ → ℂ := fun w => (1 / z ^ 2) * ((w : ℂ) ^ z * (z * (Real.log w : ℂ) - 1))
    have hd1 : ∀ w > (0 : ℝ), HasDerivAt G1 ((Real.log w : ℂ) * (w : ℂ) ^ (z - 1)) w := by
      intro w hw
      have hp := (hd_cpow w hw).fun_mul (((hd_clog w hw).const_mul z).sub_const 1)
      refine (hp.const_mul (1 / z ^ 2)).congr_deriv ?_
      have hm := hmul_cid w hw
      calc
        1 / z ^ 2 * (z * ↑w ^ (z - 1) * (z * ↑(Real.log w) - 1) + ↑w ^ z * (z * ↑w⁻¹))
          = 1 / z ^ 2 * (z * ↑w ^ (z - 1) * (z * ↑(Real.log w) - 1) + z * (↑w ^ z * ↑w⁻¹)) := by ring
        _ = 1 / z ^ 2 * (z * ↑w ^ (z - 1) * (z * ↑(Real.log w) - 1) + z * ↑w ^ (z - 1)) := by rw [hm]
        _ = ↑(Real.log w) * ↑w ^ (z - 1) := by field_simp [hz_ne]; ring
    have ht1 : Tendsto G1 (𝓝[>] 0) (𝓝 0) := by
      have t1 := (ht_cpow_log 1).const_mul z
      have t0 := ht_cpow_log 0
      have hcomb := (t1.sub t0).const_mul (1 / z ^ 2)
      simp only [mul_zero, sub_zero] at hcomb
      exact hcomb.congr fun w => by dsimp [G1]; simp only [pow_one, pow_zero]; ring
    have h1 := complex_improper_Ioc01 hd1 hdom1
      (fun w hw => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonpos (Real.log_nonpos hw.1.le hw.2), Complex.norm_cpow_eq_rpow_re_of_pos hw.1]
        simp [mul_comm])
      (ContinuousOn.mul (Complex.continuous_ofReal.continuousOn.comp (Real.continuousOn_log.mono fun w hw => hw.1.ne') (mapsTo_univ _ _))
        (fun w hw => (continuousAt_ofReal_cpow_const _ _ (Or.inr hw.1.ne')).continuousWithinAt))
      ht1
    exact ⟨h1.1, by rw [h1.2]; dsimp [G1]; simp; ring⟩
  · -- k = 2
    let G2 : ℝ → ℂ := fun w =>
      (1 / z ^ 3) * ((w : ℂ) ^ z * (z ^ 2 * ((Real.log w : ℂ) * (Real.log w : ℂ)) - 2 * z * (Real.log w : ℂ) + 2))
    have hd2 : ∀ w > (0 : ℝ), HasDerivAt G2 (((Real.log w : ℂ) * (Real.log w : ℂ)) * (w : ℂ) ^ (z - 1)) w := by
      intro w hw
      have hclog2 : HasDerivAt (fun x : ℝ => (Real.log x : ℂ) * (Real.log x : ℂ))
          (2 * (Real.log w : ℂ) * ((w⁻¹ : ℝ) : ℂ)) w :=
        ((hd_clog w hw).fun_mul (hd_clog w hw)).congr_deriv (by ring)
      have hpoly := (((hclog2.const_mul (z ^ 2)).sub ((hd_clog w hw).const_mul (2 * z))).add_const 2)
      refine (((hd_cpow w hw).fun_mul hpoly).const_mul (1 / z ^ 3)).congr_deriv ?_
      have hm := hmul_cid w hw
      calc
        1 / z ^ 3 * (z * ↑w ^ (z - 1) *
              (z ^ 2 * (↑(Real.log w) * ↑(Real.log w)) - 2 * z * ↑(Real.log w) + 2) +
            ↑w ^ z * (z ^ 2 * (2 * ↑(Real.log w) * ↑w⁻¹) - 2 * z * ↑w⁻¹))
          = 1 / z ^ 3 * (z * ↑w ^ (z - 1) *
              (z ^ 2 * (↑(Real.log w) * ↑(Real.log w)) - 2 * z * ↑(Real.log w) + 2) +
              (2 * z ^ 2 * ↑(Real.log w) - 2 * z) * (↑w ^ z * ↑w⁻¹)) := by ring
        _ = 1 / z ^ 3 * (z * ↑w ^ (z - 1) *
              (z ^ 2 * (↑(Real.log w) * ↑(Real.log w)) - 2 * z * ↑(Real.log w) + 2) +
              (2 * z ^ 2 * ↑(Real.log w) - 2 * z) * ↑w ^ (z - 1)) := by rw [hm]
        _ = (↑(Real.log w) * ↑(Real.log w)) * ↑w ^ (z - 1) := by field_simp [hz_ne]; ring
    have ht2 : Tendsto G2 (𝓝[>] 0) (𝓝 0) := by
      have t2 := (ht_cpow_log 2).const_mul (z ^ 2)
      have t1 := (ht_cpow_log 1).const_mul (2 * z)
      have t0 := (ht_cpow_log 0).const_mul 2
      have hcomb := ((t2.sub t1).add t0).const_mul (1 / z ^ 3)
      simp only [mul_zero, sub_zero, add_zero] at hcomb
      exact hcomb.congr fun w => by dsimp [G2]; simp only [sq, pow_one, pow_zero]; ring
    have h2 := complex_improper_Ioc01 hd2 hdom2
      (fun w hw => by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_cpow_eq_rpow_re_of_pos hw.1]
        have : |Real.log w| * |Real.log w| = (Real.log w) ^ 2 := by
          rw [← abs_mul, abs_of_nonneg (mul_self_nonneg _)]; ring
        rw [this]; simp [mul_comm])
      (ContinuousOn.mul
        ((Complex.continuous_ofReal.continuousOn.comp (Real.continuousOn_log.mono fun w hw => hw.1.ne') (mapsTo_univ _ _)).mul
          (Complex.continuous_ofReal.continuousOn.comp (Real.continuousOn_log.mono fun w hw => hw.1.ne') (mapsTo_univ _ _)))
        (fun w hw => (continuousAt_ofReal_cpow_const _ _ (Or.inr hw.1.ne')).continuousWithinAt))
      ht2
    exact ⟨h2.1, by rw [h2.2]; dsimp [G2]; simp; ring⟩

end GaussSmallBridge
end


open Real Complex MeasureTheory Filter Set

noncomputable section
namespace GaussSmallBridge

/-! ### Part 3: 3-term ODE recurrence, generating-function saddle-point bound, and ODE remainder -/

def bEx (ω : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => ω
  | n + 2 => (ω * bEx ω (n + 1) + 9 * bEx ω n) / ((n : ℝ) + 2)

abbrev aMaj : ℕ → ℝ := bEx 19

lemma bEx_rec (ω : ℝ) (n : ℕ) :
    ((n : ℝ) + 2) * bEx ω (n + 2) = ω * bEx ω (n + 1) + 9 * bEx ω n := by
  have hne : ((n : ℝ) + 2) ≠ 0 := by positivity
  dsimp [bEx]
  exact mul_div_cancel₀ _ hne

lemma aMaj_nonneg_and_bEx_le {ω : ℝ} (hω : |ω| ≤ 19) :
    ∀ n : ℕ, (0 ≤ aMaj n ∧ |bEx ω n| ≤ aMaj n) ∧
             (0 ≤ aMaj (n + 1) ∧ |bEx ω (n + 1)| ≤ aMaj (n + 1)) := by
  intro n
  induction n with
  | zero =>
    dsimp [aMaj, bEx]
    refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, hω⟩⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    obtain ⟨⟨ha0, hb0⟩, ⟨ha1, hb1⟩⟩ := ih
    have ha2 : 0 ≤ aMaj (n + 2) := by
      dsimp only [aMaj, bEx]
      exact div_nonneg (by linarith) (by positivity)
    refine ⟨ha2, ?_⟩
    dsimp only [aMaj, bEx]
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have hmul1 : |ω * bEx ω (n + 1)| ≤ 19 * bEx 19 (n + 1) := by
      rw [abs_mul]
      exact mul_le_mul hω hb1 (abs_nonneg _) (by norm_num)
    have hmul2 : |9 * bEx ω n| ≤ 9 * bEx 19 n := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 9)]
      exact mul_le_mul_of_nonneg_left hb0 (by norm_num)
    exact le_trans (abs_add_le _ _) (add_le_add hmul1 hmul2)

lemma aMaj_nonneg (n : ℕ) : 0 ≤ aMaj n :=
  (aMaj_nonneg_and_bEx_le (by norm_num : |(19 : ℝ)| ≤ 19) n).1.1

def majPoly : ℕ → ℝ → ℝ
  | 0, _ => 1
  | m + 1, x => majPoly m x + aMaj (m + 1) * x ^ (m + 1)

private def majPolyDeriv : ℕ → ℝ → ℝ
  | 0, _ => 0
  | m + 1, x => majPolyDeriv m x + ((m : ℝ) + 1) * aMaj (m + 1) * x ^ m

private lemma hasDerivAt_majPoly (m : ℕ) (x : ℝ) :
    HasDerivAt (majPoly m) (majPolyDeriv m x) x := by
  induction m with
  | zero => simpa [majPoly, majPolyDeriv] using hasDerivAt_const x (1 : ℝ)
  | succ m ih =>
    dsimp [majPoly, majPolyDeriv]
    have hpow : HasDerivAt (fun u : ℝ => aMaj (m + 1) * u ^ (m + 1))
        (((m : ℝ) + 1) * aMaj (m + 1) * x ^ m) x := by
      simpa [Nat.cast_add, Nat.cast_one, mul_comm, mul_left_comm, mul_assoc] using
        (hasDerivAt_pow (m + 1) x).const_mul (aMaj (m + 1))
    exact ih.add hpow

private lemma majPoly_ode_id (m : ℕ) (x : ℝ) :
    majPolyDeriv m x - (19 + 9 * x) * majPoly m x =
      -(((m : ℝ) + 1) * aMaj (m + 1) * x ^ m + 9 * aMaj m * x ^ (m + 1)) := by
  induction m with
  | zero =>
    simp [majPoly, majPolyDeriv, aMaj, bEx]
  | succ m ih =>
    have hrec := bEx_rec 19 m
    change (majPolyDeriv m x + ((m : ℝ) + 1) * aMaj (m + 1) * x ^ m) -
        (19 + 9 * x) * (majPoly m x + aMaj (m + 1) * x ^ (m + 1)) =
      -((((m + 1 : ℕ) : ℝ) + 1) * aMaj (m + 2) * x ^ (m + 1) + 9 * aMaj (m + 1) * x ^ (m + 2))
    dsimp only [aMaj] at ih ⊢
    push_cast
    linear_combination ih + x ^ (m + 1) * hrec

private lemma majPoly_le_exp (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    majPoly m x ≤ Real.exp (19 * x + 9 / 2 * x ^ 2) := by
  let G : ℝ → ℝ := fun u => Real.exp (-(19 * u + 9 / 2 * u ^ 2)) * majPoly m u
  let G' : ℝ → ℝ := fun u =>
    Real.exp (-(19 * u + 9 / 2 * u ^ 2)) *
      (majPolyDeriv m u - (19 + 9 * u) * majPoly m u)
  have hderiv : ∀ u : ℝ, HasDerivAt G (G' u) u := by
    intro u
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-(19 * t + 9 / 2 * t ^ 2)))
        (-(19 + 9 * u) * Real.exp (-(19 * u + 9 / 2 * u ^ 2))) u := by
      have hp : HasDerivAt (fun t : ℝ => -(19 * t + 9 / 2 * t ^ 2)) (-(19 + 9 * u)) u := by
        have h1 := (hasDerivAt_id u).const_mul (19 : ℝ)
        have h2 := (hasDerivAt_pow 2 u).const_mul (9 / 2 : ℝ)
        exact (h1.add h2).neg.congr_deriv (by ring)
      exact hp.exp.congr_deriv (by ring)
    exact (hexp.mul (hasDerivAt_majPoly m u)).congr_deriv (by dsimp [G']; ring)
  have hcont : Continuous G' := by
    have hm : Continuous (majPoly m) :=
      continuous_iff_continuousAt.mpr fun u => (hasDerivAt_majPoly m u).continuousAt
    have hmd : Continuous (majPolyDeriv m) := by
      clear G G' hderiv hm
      induction m with
      | zero => exact continuous_const
      | succ k ih =>
        dsimp [majPolyDeriv]
        exact ih.add (continuous_const.mul (continuous_pow k))
    dsimp [G']
    exact (Real.continuous_exp.comp (by fun_prop)).mul
      (hmd.sub ((by fun_prop : Continuous fun u : ℝ => 19 + 9 * u).mul hm))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u)
    (hcont.intervalIntegrable 0 x)
  have hG0 : G 0 = 1 := by
    dsimp [G]
    have hm0 : majPoly m 0 = 1 := by
      clear G G' hderiv hcont hftc
      induction m with
      | zero => rfl
      | succ k ih => simp [majPoly, ih]
    simp [hm0]
  have hint_le : ∫ u in (0)..x, G' u ≤ 0 := by
    rw [intervalIntegral.integral_of_le hx]
    refine setIntegral_nonpos measurableSet_Ioc fun u hu => ?_
    dsimp [G']
    rw [majPoly_ode_id]
    have hterm_nn : 0 ≤ ((m : ℝ) + 1) * aMaj (m + 1) * u ^ m + 9 * aMaj m * u ^ (m + 1) :=
      add_nonneg (mul_nonneg (mul_nonneg (by positivity) (aMaj_nonneg (m + 1))) (pow_nonneg hu.1.le _))
        (mul_nonneg (mul_nonneg (by norm_num) (aMaj_nonneg m)) (pow_nonneg hu.1.le _))
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) (neg_nonpos.mpr hterm_nn)
  have hGx : G x ≤ 1 := by linarith [hftc, hG0, hint_le]
  dsimp [G] at hGx
  have hexp_pos : 0 < Real.exp (19 * x + 9 / 2 * x ^ 2) := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_left hGx hexp_pos.le
  rwa [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul, mul_one] at hmul

private lemma majPoly_nonneg (m : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ majPoly m x := by
  induction m with
  | zero => simp [majPoly]
  | succ k ih =>
    dsimp [majPoly]
    exact add_nonneg ih (mul_nonneg (aMaj_nonneg (k + 1)) (pow_nonneg hx _))

lemma aMaj_95_96_bounds :
    aMaj 95 ≤ 1 / 50000 ∧ aMaj 96 ≤ 1 / 100000 ∧ majPoly 95 1 ≤ 3 ^ 22 := by
  have he_hi : Real.exp 1 < 2719 / 1000 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h76 : Real.exp (19 * (5 / 2 : ℝ) + 9 / 2 * (5 / 2 : ℝ) ^ 2) ≤ (2719 / 1000 : ℝ) ^ 76 := by
    have h1 : 19 * (5 / 2 : ℝ) + 9 / 2 * (5 / 2 : ℝ) ^ 2 ≤ (76 : ℕ) := by norm_num
    calc
      Real.exp (19 * (5 / 2 : ℝ) + 9 / 2 * (5 / 2 : ℝ) ^ 2)
        ≤ Real.exp ((76 : ℕ) * 1) := Real.exp_le_exp.mpr (by simpa using h1)
      _ = (Real.exp 1) ^ 76 := Real.exp_nat_mul 1 76
      _ ≤ (2719 / 1000 : ℝ) ^ 76 := pow_le_pow_left₀ (Real.exp_nonneg _) he_hi.le 76
  have hm96 := le_trans (majPoly_le_exp 96 (by norm_num : (0 : ℝ) ≤ 5 / 2)) h76
  have hm94_nn : 0 ≤ majPoly 94 (5 / 2) := majPoly_nonneg 94 (by norm_num)
  have ht96_nn : 0 ≤ aMaj 96 * (5 / 2 : ℝ) ^ 96 :=
    mul_nonneg (aMaj_nonneg 96) (by positivity)
  have ht95_nn : 0 ≤ aMaj 95 * (5 / 2 : ℝ) ^ 95 :=
    mul_nonneg (aMaj_nonneg 95) (by positivity)
  have hexp96 : majPoly 96 (5 / 2) = majPoly 94 (5 / 2) + aMaj 95 * (5 / 2) ^ 95 + aMaj 96 * (5 / 2) ^ 96 := by
    rfl
  have h95_pow : aMaj 95 * (5 / 2 : ℝ) ^ 95 ≤ (2719 / 1000 : ℝ) ^ 76 := by linarith
  have h96_pow : aMaj 96 * (5 / 2 : ℝ) ^ 96 ≤ (2719 / 1000 : ℝ) ^ 76 := by linarith
  have hnum95 : (2719 / 1000 : ℝ) ^ 76 ≤ (1 / 50000 : ℝ) * (5 / 2 : ℝ) ^ 95 := by norm_num
  have hnum96 : (2719 / 1000 : ℝ) ^ 76 ≤ (1 / 100000 : ℝ) * (5 / 2 : ℝ) ^ 96 := by norm_num
  have hb95 : aMaj 95 ≤ 1 / 50000 := by
    have hp : (0 : ℝ) < (5 / 2 : ℝ) ^ 95 := by positivity
    exact le_of_mul_le_mul_right (le_trans h95_pow hnum95) hp
  have hb96 : aMaj 96 ≤ 1 / 100000 := by
    have hp : (0 : ℝ) < (5 / 2 : ℝ) ^ 96 := by positivity
    exact le_of_mul_le_mul_right (le_trans h96_pow hnum96) hp
  have hm1 : majPoly 95 1 ≤ 3 ^ 22 := by
    have hle := majPoly_le_exp 95 (by norm_num : (0 : ℝ) ≤ 1)
    have hsq : (Real.exp (19 * (1 : ℝ) + 9 / 2 * (1 : ℝ) ^ 2)) ^ 2 ≤ ((3 : ℝ) ^ 22) ^ 2 := by
      have : (Real.exp (19 * (1 : ℝ) + 9 / 2 * (1 : ℝ) ^ 2)) ^ 2 = (Real.exp 1) ^ 47 := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; congr 1; norm_num
      rw [this]
      calc
        (Real.exp 1) ^ 47 ≤ (2719 / 1000 : ℝ) ^ 47 := pow_le_pow_left₀ (Real.exp_nonneg _) he_hi.le 47
        _ ≤ ((3 : ℝ) ^ 22) ^ 2 := by norm_num
    have hexp_le : Real.exp (19 * (1 : ℝ) + 9 / 2 * (1 : ℝ) ^ 2) ≤ 3 ^ 22 := by
      by_contra hgt; push Not at hgt
      have := pow_lt_pow_left₀ hgt (by positivity) (by norm_num : 2 ≠ 0)
      linarith
    exact le_trans hle hexp_le
  exact ⟨hb95, hb96, hm1⟩

/-! ### Complex ODE Polynomial Remainder on `[0, 1]` -/

def odePoly (ω : ℝ) : ℕ → ℝ → ℂ
  | 0, _ => 1
  | m + 1, u => odePoly ω m u + Complex.I ^ (m + 1) * (bEx ω (m + 1) : ℂ) * (u : ℂ) ^ (m + 1)

private def odePolyDeriv (ω : ℝ) : ℕ → ℝ → ℂ
  | 0, _ => 0
  | m + 1, u => odePolyDeriv ω m u + ((m : ℂ) + 1) * Complex.I ^ (m + 1) * (bEx ω (m + 1) : ℂ) * (u : ℂ) ^ m

private lemma hasDerivAt_ofReal_C3 (u : ℝ) : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 u := by
  simpa using (hasDerivAt_id u).ofReal_comp

private lemma hasDerivAt_ofReal_pow_C (k : ℕ) (u : ℝ) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ k) ((k : ℂ) * (u : ℂ) ^ (k - 1)) u := by
  induction k with
  | zero => simpa using hasDerivAt_const u (1 : ℂ)
  | succ k ih =>
    cases k with
    | zero => simpa using hasDerivAt_ofReal_C3 u
    | succ k =>
      have hp : HasDerivAt (fun x : ℝ => (x : ℂ) ^ (k + 1) * (x : ℂ))
          ((((k + 1 : ℕ) : ℂ) * (u : ℂ) ^ k) * (u : ℂ) + (u : ℂ) ^ (k + 1) * 1) u :=
        ih.fun_mul (hasDerivAt_ofReal_C3 u)
      refine (hp.congr_of_eventuallyEq (Eventually.of_forall fun x => (pow_succ (x : ℂ) (k + 1)).symm)).congr_deriv ?_
      simp only [Nat.add_sub_cancel, pow_succ, Nat.cast_add, Nat.cast_one]
      ring

private lemma hasDerivAt_odePoly (ω : ℝ) (m : ℕ) (u : ℝ) :
    HasDerivAt (odePoly ω m) (odePolyDeriv ω m u) u := by
  induction m with
  | zero => simpa [odePoly, odePolyDeriv] using hasDerivAt_const u (1 : ℂ)
  | succ m ih =>
    dsimp [odePoly, odePolyDeriv]
    have hp := (hasDerivAt_ofReal_pow_C (m + 1) u).const_mul (Complex.I ^ (m + 1) * (bEx ω (m + 1) : ℂ))
    refine ih.add (hp.congr_deriv ?_)
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring

private lemma odePoly_ode_id (ω : ℝ) (m : ℕ) (u : ℝ) :
    odePolyDeriv ω m u + (9 * (u : ℂ) - Complex.I * (ω : ℂ)) * odePoly ω m u =
      -((((m : ℂ) + 1) * Complex.I ^ (m + 1) * (bEx ω (m + 1) : ℂ) * (u : ℂ) ^ m -
          9 * Complex.I ^ m * (bEx ω m : ℂ) * (u : ℂ) ^ (m + 1))) := by
  induction m with
  | zero =>
    simp [odePoly, odePolyDeriv, bEx]
  | succ m ih =>
    have hrec : (((m : ℂ) + 2) * (bEx ω (m + 2) : ℂ)) =
        (ω : ℂ) * (bEx ω (m + 1) : ℂ) + 9 * (bEx ω m : ℂ) := by
      exact_mod_cast bEx_rec ω m
    have hI2 : Complex.I ^ (m + 2) = -(Complex.I ^ m) := by
      rw [pow_add, Complex.I_sq]; ring
    have hI1 : Complex.I * Complex.I ^ (m + 1) = Complex.I ^ (m + 2) := by
      rw [← pow_succ']
    change (odePolyDeriv ω m u + ((m : ℂ) + 1) * Complex.I ^ (m + 1) * (bEx ω (m + 1) : ℂ) * (u : ℂ) ^ m) +
        (9 * (u : ℂ) - Complex.I * (ω : ℂ)) *
          (odePoly ω m u + Complex.I ^ (m + 1) * (bEx ω (m + 1) : ℂ) * (u : ℂ) ^ (m + 1)) =
      -(((((m + 1 : ℕ) : ℂ) + 1) * Complex.I ^ (m + 2) * (bEx ω (m + 2) : ℂ) * (u : ℂ) ^ (m + 1) -
          9 * Complex.I ^ (m + 1) * (bEx ω (m + 1) : ℂ) * (u : ℂ) ^ (m + 2)))
    push_cast
    calc
      odePolyDeriv ω m u + (↑m + 1) * Complex.I ^ (m + 1) * ↑(bEx ω (m + 1)) * ↑u ^ m +
          (9 * ↑u - Complex.I * ↑ω) *
            (odePoly ω m u + Complex.I ^ (m + 1) * ↑(bEx ω (m + 1)) * ↑u ^ (m + 1))
        = (odePolyDeriv ω m u + (9 * ↑u - Complex.I * ↑ω) * odePoly ω m u) +
            (↑m + 1) * Complex.I ^ (m + 1) * ↑(bEx ω (m + 1)) * ↑u ^ m +
            9 * Complex.I ^ (m + 1) * ↑(bEx ω (m + 1)) * (↑u ^ (m + 1) * ↑u) -
            (Complex.I * Complex.I ^ (m + 1)) * ↑ω * ↑(bEx ω (m + 1)) * ↑u ^ (m + 1) := by ring
      _ = 9 * Complex.I ^ m * ↑(bEx ω m) * ↑u ^ (m + 1) +
            9 * Complex.I ^ (m + 1) * ↑(bEx ω (m + 1)) * ↑u ^ (m + 2) -
            Complex.I ^ (m + 2) * ↑ω * ↑(bEx ω (m + 1)) * ↑u ^ (m + 1) := by
          rw [ih, hI1, ← pow_succ]; ring
      _ = -(Complex.I ^ (m + 2) * (↑ω * ↑(bEx ω (m + 1)) + 9 * ↑(bEx ω m)) * ↑u ^ (m + 1) -
            9 * Complex.I ^ (m + 1) * ↑(bEx ω (m + 1)) * ↑u ^ (m + 2)) := by
          rw [hI2]; ring
      _ = -((↑m + 1 + 1) * Complex.I ^ (m + 2) * ↑(bEx ω (m + 2)) * ↑u ^ (m + 1) -
            9 * Complex.I ^ (m + 1) * ↑(bEx ω (m + 1)) * ↑u ^ (m + 2)) := by
          have hrec' : (↑ω * ↑(bEx ω (m + 1)) + 9 * ↑(bEx ω m) : ℂ) = (↑m + 1 + 1) * ↑(bEx ω (m + 2)) := by
            linear_combination -hrec
          rw [hrec']; ring

lemma norm_g0_sub_odePoly_95_le {ω w : ℝ} (hω : |ω| ≤ 19) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    ‖Complex.exp (-(9 / 2 : ℂ) * (w : ℂ) ^ 2 + Complex.I * (ω : ℂ) * (w : ℂ)) -
      odePoly ω 95 w‖ ≤ 12 / 1000000 := by
  let E_pos : ℝ → ℂ := fun u => Complex.exp (-(9 / 2 : ℂ) * (u : ℂ) ^ 2 + Complex.I * (ω : ℂ) * (u : ℂ))
  let E_inv : ℝ → ℂ := fun u => Complex.exp ((9 / 2 : ℂ) * (u : ℂ) ^ 2 - Complex.I * (ω : ℂ) * (u : ℂ))
  let H : ℝ → ℂ := fun u => 1 - E_inv u * odePoly ω 95 u
  let H' : ℝ → ℂ := fun u =>
    -E_inv u * (odePolyDeriv ω 95 u + (9 * (u : ℂ) - Complex.I * (ω : ℂ)) * odePoly ω 95 u)
  have hderiv : ∀ u : ℝ, HasDerivAt H (H' u) u := by
    intro u
    have hu2 : HasDerivAt (fun x : ℝ => (x : ℂ) ^ 2) (2 * (u : ℂ)) u := by
      simpa using hasDerivAt_ofReal_pow_C 2 u
    have hexp_arg : HasDerivAt (fun x : ℝ => (9 / 2 : ℂ) * (x : ℂ) ^ 2 - Complex.I * (ω : ℂ) * (x : ℂ))
        (9 * (u : ℂ) - Complex.I * (ω : ℂ)) u := by
      have ha := hu2.const_mul (9 / 2 : ℂ)
      have hb := (hasDerivAt_ofReal_C3 u).const_mul (Complex.I * (ω : ℂ))
      exact (ha.sub hb).congr_deriv (by ring)
    have hEinv : HasDerivAt E_inv ((9 * (u : ℂ) - Complex.I * (ω : ℂ)) * E_inv u) u :=
      hexp_arg.cexp.congr_deriv (by dsimp [E_inv]; ring)
    exact ((hEinv.fun_mul (hasDerivAt_odePoly ω 95 u)).const_sub 1).congr_deriv (by dsimp [H']; ring)
  have hcont : Continuous H' := by
    have hp : Continuous (odePoly ω 95) :=
      continuous_iff_continuousAt.mpr fun u => (hasDerivAt_odePoly ω 95 u).continuousAt
    have hpd : Continuous (odePolyDeriv ω 95) := by
      clear E_pos E_inv H H' hderiv hp
      induction (95 : ℕ) with
      | zero => exact continuous_const
      | succ k ih =>
        dsimp [odePolyDeriv]
        exact ih.add (continuous_const.mul (Complex.continuous_ofReal.pow k))
    dsimp [H', E_inv]
    exact (Complex.continuous_exp.comp (by fun_prop)).neg.mul
      (hpd.add ((by fun_prop : Continuous fun u : ℝ => 9 * (u : ℂ) - Complex.I * (ω : ℂ)).mul hp))
  have hH0 : H 0 = 0 := by
    dsimp [H, E_inv]
    have hp0 : odePoly ω 95 0 = 1 := by
      clear E_pos E_inv H H' hderiv hcont
      induction (95 : ℕ) with
      | zero => rfl
      | succ k ih => simp [odePoly, ih]
    simp [hp0]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u)
    (hcont.intervalIntegrable 0 w)
  rw [hH0, sub_zero] at hftc
  have hfac : E_pos w - odePoly ω 95 w = E_pos w * H w := by
    dsimp [H, E_pos, E_inv]
    rw [mul_sub, mul_one, ← mul_assoc, ← Complex.exp_add]
    have : -(9 / 2 : ℂ) * ↑w ^ 2 + Complex.I * ↑ω * ↑w + (9 / 2 * ↑w ^ 2 - Complex.I * ↑ω * ↑w) = 0 := by ring
    rw [this, Complex.exp_zero, one_mul]
  rw [hfac, ← hftc, ← intervalIntegral.integral_const_mul]
  have hbound : ∀ u ∈ Ioc 0 w, ‖E_pos w * H' u‖ ≤
      96 * aMaj 96 * u ^ 95 + 9 * aMaj 95 * u ^ 96 := by
    intro u hu
    have hu0 : 0 ≤ u := hu.1.le
    have huw : u ≤ w := hu.2
    dsimp only [H']
    rw [odePoly_ode_id]
    have hprod_exp : ‖E_pos w * (-E_inv u)‖ ≤ 1 := by
      rw [norm_mul, norm_neg]
      dsimp [E_pos, E_inv]
      rw [Complex.norm_exp, Complex.norm_exp]
      have hre1 : (-(9 / 2 : ℂ) * (w : ℂ) ^ 2 + Complex.I * (ω : ℂ) * (w : ℂ)).re = -(9 / 2) * w ^ 2 := by
        simp [sq]
      have hre2 : ((9 / 2 : ℂ) * (u : ℂ) ^ 2 - Complex.I * (ω : ℂ) * (u : ℂ)).re = (9 / 2) * u ^ 2 := by
        simp [sq]
      rw [hre1, hre2, ← Real.exp_add]
      apply Real.exp_le_one_iff.mpr
      have : u ^ 2 ≤ w ^ 2 := pow_le_pow_left₀ hu0 huw 2
      linarith
    have h95_cast : ((95 : ℕ) : ℂ) + 1 = 96 := by norm_num
    rw [h95_cast]
    have h1 := norm_mul_le (E_pos w * (-E_inv u))
      (-(96 * Complex.I ^ 96 * ↑(bEx ω 96) * ↑u ^ 95 -
          9 * Complex.I ^ 95 * ↑(bEx ω 95) * ↑u ^ 96))
    have hassoc : E_pos w * (-E_inv u *
        -(96 * Complex.I ^ 96 * ↑(bEx ω 96) * ↑u ^ 95 -
          9 * Complex.I ^ 95 * ↑(bEx ω 95) * ↑u ^ 96)) =
      (E_pos w * (-E_inv u)) *
        (-(96 * Complex.I ^ 96 * ↑(bEx ω 96) * ↑u ^ 95 -
          9 * Complex.I ^ 95 * ↑(bEx ω 95) * ↑u ^ 96)) := by ring
    rw [hassoc]
    have hsub_norm :
        ‖-(96 * Complex.I ^ 96 * ↑(bEx ω 96) * ↑u ^ 95 -
            9 * Complex.I ^ 95 * ↑(bEx ω 95) * ↑u ^ 96)‖ ≤
          96 * aMaj 96 * u ^ 95 + 9 * aMaj 95 * u ^ 96 := by
      rw [norm_neg]
      refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)
      · have hb96 := (aMaj_nonneg_and_bEx_le hω 95).2.2
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, norm_pow, Complex.norm_I, one_pow, mul_one,
          Complex.norm_real, Real.norm_eq_abs, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb96 (by norm_num)) (pow_nonneg hu0 95)
      · have hb95 := (aMaj_nonneg_and_bEx_le hω 95).1.2
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, norm_pow, Complex.norm_I, one_pow, mul_one,
          Complex.norm_real, Real.norm_eq_abs, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb95 (by norm_num)) (pow_nonneg hu0 96)
    exact le_trans h1 (le_trans (mul_le_mul hprod_exp hsub_norm (norm_nonneg _) zero_le_one) (by linarith))
  have hint_le : ‖∫ u in (0)..w, E_pos w * H' u‖ ≤
      ∫ u in (0)..w, (96 * aMaj 96 * u ^ 95 + 9 * aMaj 95 * u ^ 96) :=
    intervalIntegral.norm_integral_le_of_norm_le hw0 (Eventually.of_forall fun u hu => hbound u hu)
      (Continuous.intervalIntegrable (by fun_prop) 0 w)
  have hint_eval : ∫ u in (0)..w, (96 * aMaj 96 * u ^ 95 + 9 * aMaj 95 * u ^ 96) =
      aMaj 96 * w ^ 96 + (9 / 97) * aMaj 95 * w ^ 97 := by
    let P : ℝ → ℝ := fun u => aMaj 96 * u ^ 96 + (9 / 97) * aMaj 95 * u ^ 97
    have hdP : ∀ u : ℝ, HasDerivAt P (96 * aMaj 96 * u ^ 95 + 9 * aMaj 95 * u ^ 96) u := by
      intro u
      have h1 : HasDerivAt (fun x : ℝ => aMaj 96 * x ^ 96) (96 * aMaj 96 * u ^ 95) u :=
        ((hasDerivAt_pow 96 u).const_mul (aMaj 96)).congr_deriv (by push_cast; ring)
      have h2 : HasDerivAt (fun x : ℝ => (9 / 97 : ℝ) * aMaj 95 * x ^ 97) (9 * aMaj 95 * u ^ 96) u :=
        ((hasDerivAt_pow 97 u).const_mul ((9 / 97 : ℝ) * aMaj 95)).congr_deriv (by push_cast; ring)
      exact h1.add h2
    have hftcP := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hdP u)
      (Continuous.intervalIntegrable (by fun_prop) 0 w)
    rw [hftcP]
    simp [P]
  rw [hint_eval] at hint_le
  obtain ⟨ha95, ha96, _⟩ := aMaj_95_96_bounds
  have hw96 : w ^ 96 ≤ 1 := pow_le_one₀ hw0 hw1
  have hw97 : w ^ 97 ≤ 1 := pow_le_one₀ hw0 hw1
  have h1 : aMaj 96 * w ^ 96 ≤ aMaj 96 := by
    simpa using mul_le_mul_of_nonneg_left hw96 (aMaj_nonneg 96)
  have h2 : (9 / 97 : ℝ) * aMaj 95 * w ^ 97 ≤ (9 / 97) * aMaj 95 := by
    have := mul_le_mul_of_nonneg_left hw97 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 97) (aMaj_nonneg 95))
    linarith
  linarith

end GaussSmallBridge
end


open Real Complex MeasureTheory Filter Set
open scoped Topology BigOperators

noncomputable section
namespace GaussSmallBridge

/-! ### Part 4A: Full Analytic Jet Enclosure for `mellin` at `|δ₀| ≤ 1` -/

def pi0R : ℝ := (314159265359 : ℝ) / 100000000000

def polyJ0 (ω : ℝ) (s₀ : ℂ) : ℂ :=
  ∑ n ∈ Finset.range 96, Complex.I ^ n * (bEx ω n : ℂ) * (1 / (s₀ + (n : ℂ)))

def polyJdRaw (ω : ℝ) (s₀ : ℂ) : ℂ :=
  ∑ n ∈ Finset.range 96, Complex.I ^ n * (bEx ω n : ℂ) * (1 / (s₀ + (n : ℂ) + 1))

def polyJt (ω : ℝ) (s₀ : ℂ) : ℂ :=
  ∑ n ∈ Finset.range 96, Complex.I ^ n * (bEx ω n : ℂ) * (-Complex.I / (s₀ + (n : ℂ)) ^ 2)

def polyJt2 (ω : ℝ) (s₀ : ℂ) : ℂ :=
  ∑ n ∈ Finset.range 96, Complex.I ^ n * (bEx ω n : ℂ) * (-1 / (s₀ + (n : ℂ)) ^ 3)

def mellinVal (δ : ℝ) (s : ℂ) : ℂ :=
  mellin (fun u : ℝ => (Real.exp (-u ^ 2 / 2) : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ))) s

def G3 (δ t : ℝ) : ℂ :=
  ∫ w : ℝ in Ioc (0 : ℝ) 1,
    (w : ℂ) ^ (((1 / 2 : ℂ) + (t : ℝ) * Complex.I) - 1) *
      Complex.exp (-(9 / 2 : ℂ) * (w : ℂ) ^ 2 + 6 * Real.pi * Complex.I * (δ : ℂ) * (w : ℂ))

lemma pi_approx_pi0R :
    Real.pi ≤ pi0R ∧ |Real.pi - pi0R| ≤ 1 / 10 ^ 11 ∧ Real.pi < 315 / 100 ∧ 6 * pi0R ≤ 19 := by
  have hgt := Real.pi_gt_d20
  have hlt := Real.pi_lt_d20
  dsimp [pi0R]
  refine ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩, by linarith, by norm_num⟩

lemma pi0R_pos : 0 < pi0R := by
  dsimp [pi0R]; norm_num

private lemma odePoly_95_eq_sum (ω w : ℝ) :
    odePoly ω 95 w = ∑ n ∈ Finset.range 96, Complex.I ^ n * (bEx ω n : ℂ) * (w : ℂ) ^ n := by
  have hgen : ∀ m : ℕ, odePoly ω m w =
      ∑ n ∈ Finset.range (m + 1), Complex.I ^ n * (bEx ω n : ℂ) * (w : ℂ) ^ n := by
    intro m
    induction m with
    | zero => simp [odePoly, bEx]
    | succ k ih =>
      rw [Finset.sum_range_succ]
      dsimp [odePoly]
      rw [ih]
  exact hgen 95

private lemma integrableOn_sum_range {E : Type*} [NormedAddCommGroup E] {s : Set ℝ}
    (N : ℕ) (term : ℕ → ℝ → E) (h : ∀ n, IntegrableOn (term n) s) :
    IntegrableOn (fun w => ∑ n ∈ Finset.range N, term n w) s := by
  induction N with
  | zero => simp
  | succ k ih =>
    simp_rw [Finset.sum_range_succ]
    exact ih.add (h k)

lemma mellinVal_split_G3 (δ t : ℝ) :
    let s : ℂ := (1 / 2 : ℂ) + (t : ℝ) * Complex.I
    ‖mellinVal δ s‖ ≤ Real.sqrt 3 * (‖G3 δ t‖ + 1 / 801) ∧
    Real.sqrt 3 * (‖G3 δ t‖ - 1 / 801) ≤ ‖mellinVal δ s‖ := by
  intro s
  let f : ℝ → ℂ := fun u =>
    (u : ℂ) ^ (s - 1) * ((Real.exp (-u ^ 2 / 2) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ)))
  obtain ⟨hf_int3, htail_le⟩ := tail3_int_and_bound δ t
  have hf_int03 : IntegrableOn f (Ioc (0 : ℝ) 3) := by
    have hgam_ioi : IntegrableOn (fun u : ℝ => Real.exp (1 / 2) * (Real.exp (-u) * u ^ (1 / 2 - 1 : ℝ))) (Ioi 0) :=
      (Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (Real.exp (1 / 2))
    have hgam : IntegrableOn (fun u : ℝ => Real.exp (1 / 2) * (Real.exp (-u) * u ^ (1 / 2 - 1 : ℝ))) (Ioc (0 : ℝ) 3) :=
      hgam_ioi.mono_set Ioc_subset_Ioi_self
    have hf_meas : AEStronglyMeasurable f (volume.restrict (Ioc (0 : ℝ) 3)) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      refine ContinuousOn.mul (fun u hu => (continuousAt_ofReal_cpow_const _ _ (Or.inr hu.1.ne')).continuousWithinAt)
        (Continuous.continuousOn (by fun_prop))
    refine hgam.mono' hf_meas ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with u hu
    dsimp [f]
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu.1, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_nonneg _)]
    have hcexp : ‖Complex.exp (2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ))‖ = 1 := by
      have : 2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ) =
          ((2 * Real.pi * (δ * u) : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    have hs1 : (s - 1).re = 1 / 2 - 1 := by simp [s]
    rw [hcexp, mul_one, hs1]
    have hexp_le : Real.exp (-u ^ 2 / 2) ≤ Real.exp (1 / 2) * Real.exp (-u) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : 0 ≤ (u - 1) ^ 2 := sq_nonneg (u - 1)
      linarith
    calc
      u ^ (1 / 2 - 1 : ℝ) * Real.exp (-u ^ 2 / 2)
        ≤ u ^ (1 / 2 - 1 : ℝ) * (Real.exp (1 / 2) * Real.exp (-u)) :=
          mul_le_mul_of_nonneg_left hexp_le (Real.rpow_nonneg hu.1.le _)
      _ = Real.exp (1 / 2) * (Real.exp (-u) * u ^ (1 / 2 - 1 : ℝ)) := by ring
  have hmellin_eq : mellinVal δ s = (∫ u : ℝ in Ioc (0 : ℝ) 3, f u) + (∫ u : ℝ in Ioi (3 : ℝ), f u) := by
    dsimp [mellinVal]
    unfold mellin
    have h_f : (fun u : ℝ => (u : ℂ) ^ (s - 1) •
        ((Real.exp (-u ^ 2 / 2) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ)))) = f := by
      ext u; simp [f, smul_eq_mul]
    change ∫ u : ℝ in Ioi (0 : ℝ), _ = _
    rw [h_f, ← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 3)]
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hf_int03 hf_int3
  have h03_eq : (∫ u : ℝ in Ioc (0 : ℝ) 3, f u) = (3 : ℂ) ^ s * G3 δ t := by
    have hiv := intervalIntegral.integral_comp_mul_left (f := f) (c := (3 : ℝ)) (by norm_num : (3 : ℝ) ≠ 0) (a := 0) (b := 1)
    simp only [mul_zero, mul_one] at hiv
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 3)]
    have h3_smul : ∫ u in (0)..3, f u = (3 : ℂ) * ∫ w in (0)..1, f (3 * w) := by
      have := congrArg ((3 : ℝ) • ·) hiv
      rw [smul_smul, mul_inv_cancel₀ (by norm_num : (3 : ℝ) ≠ 0), one_smul] at this
      rw [← this, Complex.real_smul, Complex.ofReal_ofNat]
    rw [h3_smul, intervalIntegral.integral_of_le zero_le_one, ← integral_const_mul]
    dsimp [G3]
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun w hw => ?_
    have hw0 : 0 < w := hw.1
    dsimp [f]
    have hcpow : ((3 * w : ℝ) : ℂ) ^ (s - 1) = (3 : ℂ) ^ (s - 1) * (w : ℂ) ^ (s - 1) := by
      rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by norm_num) hw0.le, Complex.ofReal_ofNat]
    have h3s : (3 : ℂ) * (3 : ℂ) ^ (s - 1) = (3 : ℂ) ^ s := by
      calc
        (3 : ℂ) * (3 : ℂ) ^ (s - 1) = (3 : ℂ) ^ (1 : ℂ) * (3 : ℂ) ^ (s - 1) := by rw [Complex.cpow_one]
        _ = (3 : ℂ) ^ s := by rw [← Complex.cpow_add _ _ (by norm_num)]; congr 1; ring
    have hexp : ((Real.exp (-(3 * w) ^ 2 / 2) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((δ * (3 * w) : ℝ) : ℂ))) =
        Complex.exp (-(9 / 2 : ℂ) * (w : ℂ) ^ 2 + 6 * Real.pi * Complex.I * (δ : ℂ) * (w : ℂ)) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1; push_cast; ring
    rw [hcpow, hexp]
    calc
      (3 : ℂ) * ((3 : ℂ) ^ (s - 1) * ↑w ^ (s - 1) *
          cexp (-(9 / 2) * ↑w ^ 2 + 6 * ↑Real.pi * Complex.I * ↑δ * ↑w))
        = ((3 : ℂ) * (3 : ℂ) ^ (s - 1)) *
            (↑w ^ (s - 1) * cexp (-(9 / 2) * ↑w ^ 2 + 6 * ↑Real.pi * Complex.I * ↑δ * ↑w)) := by ring
      _ = (3 : ℂ) ^ s *
            (↑w ^ (s - 1) * cexp (-(9 / 2) * ↑w ^ 2 + 6 * ↑Real.pi * Complex.I * ↑δ * ↑w)) := by rw [h3s]
  rw [hmellin_eq, h03_eq]
  have hnorm3s : ‖(3 : ℂ) ^ s‖ = Real.sqrt 3 := by
    have : (3 : ℂ) = ((3 : ℝ) : ℂ) := by norm_num
    rw [this, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 3)]
    have hsre : s.re = 1 / 2 := by simp [s]
    rw [hsre, ← Real.sqrt_eq_rpow]
  refine ⟨?_, ?_⟩
  · calc
      ‖(3 : ℂ) ^ s * G3 δ t + ∫ u : ℝ in Ioi (3 : ℝ), f u‖
        ≤ ‖(3 : ℂ) ^ s * G3 δ t‖ + ‖∫ u : ℝ in Ioi (3 : ℝ), f u‖ := norm_add_le _ _
      _ = Real.sqrt 3 * ‖G3 δ t‖ + ‖∫ u : ℝ in Ioi (3 : ℝ), f u‖ := by rw [norm_mul, hnorm3s]
      _ ≤ Real.sqrt 3 * ‖G3 δ t‖ + Real.sqrt 3 * (1 / 801) := add_le_add_right htail_le _
      _ = Real.sqrt 3 * (‖G3 δ t‖ + 1 / 801) := by ring
  · have htri : ‖(3 : ℂ) ^ s * G3 δ t‖ ≤
        ‖(3 : ℂ) ^ s * G3 δ t + ∫ u : ℝ in Ioi (3 : ℝ), f u‖ + ‖∫ u : ℝ in Ioi (3 : ℝ), f u‖ := by
      simpa using norm_add_le ((3 : ℂ) ^ s * G3 δ t + ∫ u : ℝ in Ioi (3 : ℝ), f u) (-(∫ u : ℝ in Ioi (3 : ℝ), f u))
    rw [norm_mul, hnorm3s] at htri
    linarith

private lemma poly_integrals_eq (ω t₀ : ℝ) :
    let s₀ : ℂ := (1 / 2 : ℂ) + (t₀ : ℝ) * Complex.I
    let P : ℝ → ℂ := odePoly ω 95
    (IntegrableOn (fun w : ℝ => (w : ℂ) ^ (s₀ - 1) * P w) (Ioc (0 : ℝ) 1) ∧
      ∫ w : ℝ in Ioc (0 : ℝ) 1, (w : ℂ) ^ (s₀ - 1) * P w = polyJ0 ω s₀) ∧
    (IntegrableOn (fun w : ℝ => (w : ℂ) ^ s₀ * P w) (Ioc (0 : ℝ) 1) ∧
      ∫ w : ℝ in Ioc (0 : ℝ) 1, (w : ℂ) ^ s₀ * P w = polyJdRaw ω s₀) ∧
    (IntegrableOn (fun w : ℝ => Complex.I * (Real.log w : ℂ) * (w : ℂ) ^ (s₀ - 1) * P w) (Ioc (0 : ℝ) 1) ∧
      ∫ w : ℝ in Ioc (0 : ℝ) 1, Complex.I * (Real.log w : ℂ) * (w : ℂ) ^ (s₀ - 1) * P w = polyJt ω s₀) ∧
    (IntegrableOn (fun w : ℝ => -(1 / 2 : ℂ) * ((Real.log w : ℂ) * (Real.log w : ℂ)) * (w : ℂ) ^ (s₀ - 1) * P w) (Ioc (0 : ℝ) 1) ∧
      ∫ w : ℝ in Ioc (0 : ℝ) 1, -(1 / 2 : ℂ) * ((Real.log w : ℂ) * (Real.log w : ℂ)) * (w : ℂ) ^ (s₀ - 1) * P w = polyJt2 ω s₀) := by
  intro s₀ P
  have hre : ∀ n : ℕ, 0 < (s₀ + (n : ℂ)).re := fun n => by
    simp [s₀]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hre1 : ∀ n : ℕ, 0 < (s₀ + (n : ℂ) + 1).re := fun n => by
    simp [s₀]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hw_pow : ∀ (w : ℝ), 0 < w → ∀ (z : ℂ) (n : ℕ), (w : ℂ) ^ (z - 1) * (w : ℂ) ^ n = (w : ℂ) ^ (z + (n : ℂ) - 1) := by
    intro w hw z n
    have hw_ne : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hw_ne]
    congr 1; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- J0
    let term : ℕ → ℝ → ℂ := fun n w => Complex.I ^ n * (bEx ω n : ℂ) * (w : ℂ) ^ (s₀ + (n : ℂ) - 1)
    have hterm : ∀ n, IntegrableOn (term n) (Ioc (0 : ℝ) 1) ∧ ∫ w : ℝ in Ioc (0 : ℝ) 1, term n w =
        Complex.I ^ n * (bEx ω n : ℂ) * (1 / (s₀ + (n : ℂ))) := by
      intro n
      obtain ⟨⟨hi, hv⟩, _, _⟩ := complex_integral_cpow_log_Ioc (hre n)
      exact ⟨hi.const_mul _, by dsimp [term]; rw [integral_const_mul, hv]⟩
    have hcongr : EqOn (fun w : ℝ => (w : ℂ) ^ (s₀ - 1) * P w) (fun w : ℝ => ∑ n ∈ Finset.range 96, term n w) (Ioc (0 : ℝ) 1) := by
      intro w hw
      dsimp [P, term]
      rw [odePoly_95_eq_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      have := hw_pow w hw.1 s₀ n
      calc
        ↑w ^ (s₀ - 1) * (Complex.I ^ n * ↑(bEx ω n) * ↑w ^ n)
          = Complex.I ^ n * ↑(bEx ω n) * (↑w ^ (s₀ - 1) * ↑w ^ n) := by ring
        _ = Complex.I ^ n * ↑(bEx ω n) * ↑w ^ (s₀ + ↑n - 1) := by rw [this]
    have hint_sum := integrableOn_sum_range 96 term fun n => (hterm n).1
    refine ⟨hint_sum.congr_fun hcongr.symm measurableSet_Ioc, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioc hcongr, integral_finsetSum _ fun n _ => (hterm n).1]
    dsimp [polyJ0]
    exact Finset.sum_congr rfl fun n _ => (hterm n).2
  · -- JdRaw
    let term : ℕ → ℝ → ℂ := fun n w => Complex.I ^ n * (bEx ω n : ℂ) * (w : ℂ) ^ (s₀ + (n : ℂ) + 1 - 1)
    have hterm : ∀ n, IntegrableOn (term n) (Ioc (0 : ℝ) 1) ∧ ∫ w : ℝ in Ioc (0 : ℝ) 1, term n w =
        Complex.I ^ n * (bEx ω n : ℂ) * (1 / (s₀ + (n : ℂ) + 1)) := by
      intro n
      obtain ⟨⟨hi, hv⟩, _, _⟩ := complex_integral_cpow_log_Ioc (hre1 n)
      exact ⟨hi.const_mul _, by dsimp [term]; rw [integral_const_mul, hv]⟩
    have hcongr : EqOn (fun w : ℝ => (w : ℂ) ^ s₀ * P w) (fun w : ℝ => ∑ n ∈ Finset.range 96, term n w) (Ioc (0 : ℝ) 1) := by
      intro w hw
      dsimp [P, term]
      rw [odePoly_95_eq_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      have := hw_pow w hw.1 (s₀ + 1) n
      have hs01 : s₀ + 1 - 1 = s₀ := by ring
      have hs02 : s₀ + 1 + (n : ℂ) - 1 = s₀ + (n : ℂ) + 1 - 1 := by ring
      rw [hs01, hs02] at this
      calc
        ↑w ^ s₀ * (Complex.I ^ n * ↑(bEx ω n) * ↑w ^ n)
          = Complex.I ^ n * ↑(bEx ω n) * (↑w ^ s₀ * ↑w ^ n) := by ring
        _ = Complex.I ^ n * ↑(bEx ω n) * ↑w ^ (s₀ + ↑n + 1 - 1) := by rw [this]
    have hint_sum := integrableOn_sum_range 96 term fun n => (hterm n).1
    refine ⟨hint_sum.congr_fun hcongr.symm measurableSet_Ioc, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioc hcongr, integral_finsetSum _ fun n _ => (hterm n).1]
    dsimp [polyJdRaw]
    exact Finset.sum_congr rfl fun n _ => (hterm n).2
  · -- Jt
    let term : ℕ → ℝ → ℂ := fun n w =>
      (Complex.I ^ n * (bEx ω n : ℂ) * Complex.I) * ((Real.log w : ℂ) * (w : ℂ) ^ (s₀ + (n : ℂ) - 1))
    have hterm : ∀ n, IntegrableOn (term n) (Ioc (0 : ℝ) 1) ∧ ∫ w : ℝ in Ioc (0 : ℝ) 1, term n w =
        Complex.I ^ n * (bEx ω n : ℂ) * (-Complex.I / (s₀ + (n : ℂ)) ^ 2) := by
      intro n
      obtain ⟨_, ⟨hi, hv⟩, _⟩ := complex_integral_cpow_log_Ioc (hre n)
      refine ⟨hi.const_mul _, ?_⟩
      dsimp [term]; rw [integral_const_mul, hv]; ring
    have hcongr : EqOn (fun w : ℝ => Complex.I * (Real.log w : ℂ) * (w : ℂ) ^ (s₀ - 1) * P w)
        (fun w : ℝ => ∑ n ∈ Finset.range 96, term n w) (Ioc (0 : ℝ) 1) := by
      intro w hw
      dsimp [P, term]
      rw [odePoly_95_eq_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      have := hw_pow w hw.1 s₀ n
      calc
        Complex.I * ↑(Real.log w) * ↑w ^ (s₀ - 1) * (Complex.I ^ n * ↑(bEx ω n) * ↑w ^ n)
          = (Complex.I ^ n * ↑(bEx ω n) * Complex.I) * (↑(Real.log w) * (↑w ^ (s₀ - 1) * ↑w ^ n)) := by ring
        _ = (Complex.I ^ n * ↑(bEx ω n) * Complex.I) * (↑(Real.log w) * ↑w ^ (s₀ + ↑n - 1)) := by rw [this]
    have hint_sum := integrableOn_sum_range 96 term fun n => (hterm n).1
    refine ⟨hint_sum.congr_fun hcongr.symm measurableSet_Ioc, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioc hcongr, integral_finsetSum _ fun n _ => (hterm n).1]
    dsimp [polyJt]
    exact Finset.sum_congr rfl fun n _ => (hterm n).2
  · -- Jt2
    let term : ℕ → ℝ → ℂ := fun n w =>
      (Complex.I ^ n * (bEx ω n : ℂ) * (-(1 / 2 : ℂ))) *
        (((Real.log w : ℂ) * (Real.log w : ℂ)) * (w : ℂ) ^ (s₀ + (n : ℂ) - 1))
    have hterm : ∀ n, IntegrableOn (term n) (Ioc (0 : ℝ) 1) ∧ ∫ w : ℝ in Ioc (0 : ℝ) 1, term n w =
        Complex.I ^ n * (bEx ω n : ℂ) * (-1 / (s₀ + (n : ℂ)) ^ 3) := by
      intro n
      obtain ⟨_, _, ⟨hi, hv⟩⟩ := complex_integral_cpow_log_Ioc (hre n)
      refine ⟨hi.const_mul _, ?_⟩
      dsimp [term]; rw [integral_const_mul, hv]; ring
    have hcongr : EqOn (fun w : ℝ => -(1 / 2 : ℂ) * ((Real.log w : ℂ) * (Real.log w : ℂ)) * (w : ℂ) ^ (s₀ - 1) * P w)
        (fun w : ℝ => ∑ n ∈ Finset.range 96, term n w) (Ioc (0 : ℝ) 1) := by
      intro w hw
      dsimp [P, term]
      rw [odePoly_95_eq_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      have := hw_pow w hw.1 s₀ n
      calc
        -(1 / 2 : ℂ) * (↑(Real.log w) * ↑(Real.log w)) * ↑w ^ (s₀ - 1) *
            (Complex.I ^ n * ↑(bEx ω n) * ↑w ^ n)
          = (Complex.I ^ n * ↑(bEx ω n) * -(1 / 2 : ℂ)) *
              ((↑(Real.log w) * ↑(Real.log w)) * (↑w ^ (s₀ - 1) * ↑w ^ n)) := by ring
        _ = (Complex.I ^ n * ↑(bEx ω n) * -(1 / 2 : ℂ)) *
              ((↑(Real.log w) * ↑(Real.log w)) * ↑w ^ (s₀ + ↑n - 1)) := by rw [this]
    have hint_sum := integrableOn_sum_range 96 term fun n => (hterm n).1
    refine ⟨hint_sum.congr_fun hcongr.symm measurableSet_Ioc, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioc hcongr, integral_finsetSum _ fun n _ => (hterm n).1]
    dsimp [polyJt2]
    exact Finset.sum_congr rfl fun n _ => (hterm n).2

attribute [irreducible] odePoly polyJ0 polyJdRaw polyJt polyJt2

private lemma exp_neg_92_le_one (w : ℝ) : Real.exp (-(9 / 2) * w ^ 2) ≤ 1 :=
  Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg w])

lemma G3_jet_approx {δ₀ : ℝ} (hδ₀ : |δ₀| ≤ 1) (hδ t₀ ht : ℝ) :
    let ω : ℝ := 6 * pi0R * δ₀
    let s₀ : ℂ := (1 / 2 : ℂ) + (t₀ : ℝ) * Complex.I
    ‖G3 (δ₀ + hδ) (t₀ + ht) -
      (polyJ0 ω s₀ + (ht : ℂ) * polyJt ω s₀ + ((ht ^ 2 : ℝ) : ℂ) * polyJt2 ω s₀)‖ ≤
      (242 / 10000000 : ℝ) +
      |hδ| * ((6 * pi0R) * ‖polyJdRaw ω s₀‖ + (1 / 6000 : ℝ)) +
      |ht| * (1 / 20000 : ℝ) +
      ht ^ 2 * (1 / 10000 : ℝ) +
      40 * hδ ^ 2 + 10 * |ht| * |hδ| + 16 * |ht| ^ 3 := by
  intro ω s₀
  obtain ⟨hpi_le_pi0, hpi_diff, hpi_lt_315, h6pi0_le19⟩ := pi_approx_pi0R
  have hω : |ω| ≤ 19 := by
    dsimp [ω]
    have h6_pos : (0 : ℝ) < 6 * pi0R := by dsimp [pi0R]; norm_num
    rw [abs_mul, abs_of_pos h6_pos]
    have := mul_le_mul_of_nonneg_left hδ₀ h6_pos.le
    linarith
  obtain ⟨⟨hP0_int, hP0_val⟩, ⟨hPd_int, hPd_val⟩, ⟨hPt_int, hPt_val⟩, ⟨hPt2_int, hPt2_val⟩⟩ :=
    poly_integrals_eq ω t₀
  obtain ⟨⟨hr0_int, hr0_val⟩, ⟨hr1_int, hr1_val⟩, ⟨hr2_int, hr2_val⟩, ⟨hr3_int, hr3_val⟩⟩ :=
    real_integral_rpow_neg_log_pow_Ioc (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨⟨hr32_0_int, hr32_0_val⟩, ⟨hr32_1_int, hr32_1_val⟩, _, _⟩ :=
    real_integral_rpow_neg_log_pow_Ioc (by norm_num : (0 : ℝ) < 3 / 2)
  let gTrue : ℝ → ℂ := fun w =>
    Complex.exp (-(9 / 2 : ℂ) * (w : ℂ) ^ 2 + 6 * Real.pi * Complex.I * (δ₀ : ℂ) * (w : ℂ))
  let g0 : ℝ → ℂ := fun w =>
    Complex.exp (-(9 / 2 : ℂ) * (w : ℂ) ^ 2 + Complex.I * (ω : ℂ) * (w : ℂ))
  let P : ℝ → ℂ := odePoly ω 95
  have hg_diff : ∀ w ∈ Ioc (0 : ℝ) 1, ‖gTrue w - P w‖ ≤ 121 / 10000000 := by
    intro w hw
    have h1 : ‖gTrue w - g0 w‖ ≤ 6 / 10 ^ 11 := by
      dsimp [gTrue, g0]
      have hfac : cexp (-(9 / 2) * ↑w ^ 2 + 6 * ↑Real.pi * Complex.I * ↑δ₀ * ↑w) -
          cexp (-(9 / 2) * ↑w ^ 2 + Complex.I * ↑ω * ↑w) =
          cexp (-(9 / 2) * ↑w ^ 2 + Complex.I * ↑ω * ↑w) *
            (cexp (Complex.I * ↑(6 * (Real.pi - pi0R) * δ₀ * w)) - 1) := by
        rw [mul_sub, mul_one, ← Complex.exp_add]
        congr 2; dsimp [ω]; push_cast; ring
      rw [hfac, norm_mul, Complex.norm_exp]
      have hre : (-(9 / 2 : ℂ) * (w : ℂ) ^ 2 + Complex.I * (ω : ℂ) * (w : ℂ)).re = -(9 / 2) * w ^ 2 := by
        simp [sq]
      rw [hre]
      have hexp1 : Real.exp (-(9 / 2) * w ^ 2) ≤ 1 := exp_neg_92_le_one w
      have hsub := norm_cexp_I_sub_T0 (6 * (Real.pi - pi0R) * δ₀ * w)
      have habs : |6 * (Real.pi - pi0R) * δ₀ * w| ≤ 6 / 10 ^ 11 := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6), abs_of_pos hw.1]
        have hdw : |δ₀| * w ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hw.2 (abs_nonneg _)) (by linarith only [hδ₀])
        have hp_dw := mul_le_mul hpi_diff hdw (mul_nonneg (abs_nonneg _) hw.1.le) (by norm_num)
        linarith only [hp_dw]
      exact le_trans (mul_le_mul hexp1 (le_trans hsub habs) (norm_nonneg _) zero_le_one) (one_mul _).le
    have h2 := norm_g0_sub_odePoly_95_le hω hw.1.le hw.2
    calc
      ‖gTrue w - P w‖ ≤ ‖gTrue w - g0 w‖ + ‖g0 w - P w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 6 / 10 ^ 11 + 12 / 1000000 := add_le_add h1 h2
      _ ≤ 121 / 10000000 := by norm_num
  have hw_norm : ∀ w ∈ Ioc (0 : ℝ) 1, ‖(w : ℂ) ^ (s₀ - 1)‖ = w ^ (1 / 2 - 1 : ℝ) := by
    intro w hw
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hw.1]
    have : (s₀ - 1).re = 1 / 2 - 1 := by simp [s₀]
    rw [this]
  have hgTrue_norm : ∀ w : ℝ, ‖gTrue w‖ = Real.exp (-(9 / 2) * w ^ 2) := by
    intro w
    dsimp [gTrue]
    rw [Complex.norm_exp]
    have : (-(9 / 2 : ℂ) * (w : ℂ) ^ 2 + 6 * Real.pi * Complex.I * (δ₀ : ℂ) * (w : ℂ)).re =
        -(9 / 2) * w ^ 2 := by
      have h6 : (6 : ℂ) * ↑Real.pi * Complex.I * ↑δ₀ * ↑w = ↑(6 * Real.pi * δ₀ * w) * Complex.I := by
        push_cast; ring
      rw [h6]; simp [sq]
    rw [this]
  let fFull : ℝ → ℂ := fun w =>
    (w : ℂ) ^ (((1 / 2 : ℂ) + ((t₀ + ht : ℝ) : ℂ) * Complex.I) - 1) *
      Complex.exp (-(9 / 2 : ℂ) * (w : ℂ) ^ 2 + 6 * Real.pi * Complex.I * ((δ₀ + hδ : ℝ) : ℂ) * (w : ℂ))
  let f0 : ℝ → ℂ := fun w => (w : ℂ) ^ (s₀ - 1) * gTrue w
  let ft : ℝ → ℂ := fun w => (ht : ℂ) * (Complex.I * (Real.log w : ℂ) * (w : ℂ) ^ (s₀ - 1) * gTrue w)
  let ft2 : ℝ → ℂ := fun w =>
    ((ht ^ 2 : ℝ) : ℂ) * (-(1 / 2 : ℂ) * ((Real.log w : ℂ) * (Real.log w : ℂ)) * (w : ℂ) ^ (s₀ - 1) * gTrue w)
  let fd : ℝ → ℂ := fun w => (hδ : ℂ) * (6 * Real.pi * Complex.I * ((w : ℂ) ^ s₀ * gTrue w))
  have hc_wp : ContinuousOn (fun w : ℝ => (w : ℂ) ^ (s₀ - 1)) (Ioc (0 : ℝ) 1) :=
    fun w hw => (continuousAt_ofReal_cpow_const _ _ (Or.inr hw.1.ne')).continuousWithinAt
  have hc_ws0 : ContinuousOn (fun w : ℝ => (w : ℂ) ^ s₀) (Ioc (0 : ℝ) 1) :=
    fun w hw => (continuousAt_ofReal_cpow_const _ _ (Or.inr hw.1.ne')).continuousWithinAt
  have hc_log : ContinuousOn (fun w : ℝ => (Real.log w : ℂ)) (Ioc (0 : ℝ) 1) :=
    Complex.continuous_ofReal.continuousOn.comp (Real.continuousOn_log.mono fun w hw => hw.1.ne') (mapsTo_univ _ _)
  have hc_gT : ContinuousOn gTrue (Ioc (0 : ℝ) 1) := Continuous.continuousOn (by dsimp [gTrue]; fun_prop)
  have hfFull_int : IntegrableOn fFull (Ioc (0 : ℝ) 1) := by
    refine hr0_int.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      refine ContinuousOn.mul (fun w hw => (continuousAt_ofReal_cpow_const _ _ (Or.inr hw.1.ne')).continuousWithinAt)
        (Continuous.continuousOn (by fun_prop))
    · rw [ae_restrict_iff' measurableSet_Ioc]; filter_upwards with w hw
      dsimp [fFull]
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hw.1, Complex.norm_exp]
      have hre1 : (((1 / 2 : ℂ) + ((t₀ + ht : ℝ) : ℂ) * Complex.I) - 1).re = 1 / 2 - 1 := by simp
      have hre2 : (-(9 / 2 : ℂ) * (w : ℂ) ^ 2 + 6 * (Real.pi : ℂ) * Complex.I * ((δ₀ + hδ : ℝ) : ℂ) * (w : ℂ)).re = -(9 / 2) * w ^ 2 := by
        have h6 : (6 : ℂ) * (Real.pi : ℂ) * Complex.I * ((δ₀ + hδ : ℝ) : ℂ) * (w : ℂ) =
            ((6 * Real.pi * (δ₀ + hδ) * w : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [h6]; simp [sq]
      rw [hre1, hre2]
      exact le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg w]))
        (Real.rpow_nonneg hw.1.le _)) (mul_one _).le
  have hf0_int : IntegrableOn f0 (Ioc (0 : ℝ) 1) := by
    refine hr0_int.mono' ((hc_wp.mul hc_gT).aestronglyMeasurable measurableSet_Ioc) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]; filter_upwards with w hw
    dsimp [f0]; rw [norm_mul, hw_norm w hw, hgTrue_norm]
    exact le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg w]))
      (Real.rpow_nonneg hw.1.le _)) (mul_one _).le
  have hft_int : IntegrableOn ft (Ioc (0 : ℝ) 1) := by
    refine (hr1_int.const_mul |ht|).mono'
      ((continuousOn_const.mul (((continuousOn_const.mul hc_log).mul hc_wp).mul hc_gT)).aestronglyMeasurable measurableSet_Ioc) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]; filter_upwards with w hw
    dsimp [ft]
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (Real.log_nonpos hw.1.le hw.2),
      hw_norm w hw, hgTrue_norm]
    have hexp1 : Real.exp (-(9 / 2) * w ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg w])
    calc
      |ht| * (-Real.log w * w ^ (1 / 2 - 1 : ℝ) * Real.exp (-(9 / 2) * w ^ 2))
        ≤ |ht| * (-Real.log w * w ^ (1 / 2 - 1 : ℝ) * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp1
            (mul_nonneg (neg_nonneg.mpr (Real.log_nonpos hw.1.le hw.2)) (Real.rpow_nonneg hw.1.le _)))
            (abs_nonneg _)
      _ = |ht| * (w ^ (1 / 2 - 1 : ℝ) * -Real.log w) := by ring
  have hft2_int : IntegrableOn ft2 (Ioc (0 : ℝ) 1) := by
    refine (hr2_int.const_mul ((1 / 2) * ht ^ 2)).mono'
      ((continuousOn_const.mul (((continuousOn_const.mul (hc_log.mul hc_log)).mul hc_wp).mul hc_gT)).aestronglyMeasurable measurableSet_Ioc) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]; filter_upwards with w hw
    dsimp [ft2]
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_neg, norm_div, norm_one, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ht),
      norm_mul, Complex.norm_real, Real.norm_eq_abs, hw_norm w hw, hgTrue_norm]
    have hexp1 : Real.exp (-(9 / 2) * w ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg w])
    have hll : |Real.log w| * |Real.log w| = (Real.log w) ^ 2 := by
      rw [← abs_mul, abs_of_nonneg (mul_self_nonneg _)]; ring
    rw [hll]
    calc
      ht ^ 2 * (1 / 2 * (Real.log w) ^ 2 * w ^ (1 / 2 - 1 : ℝ) * Real.exp (-(9 / 2) * w ^ 2))
        ≤ ht ^ 2 * (1 / 2 * (Real.log w) ^ 2 * w ^ (1 / 2 - 1 : ℝ) * 1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hexp1
              (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (Real.rpow_nonneg hw.1.le _)))
            (sq_nonneg _)
      _ = 1 / 2 * ht ^ 2 * (w ^ (1 / 2 - 1 : ℝ) * (Real.log w) ^ 2) := by ring
  have hws0_gT_int : IntegrableOn (fun w : ℝ => (w : ℂ) ^ s₀ * gTrue w) (Ioc (0 : ℝ) 1) := by
    refine hr32_0_int.mono' ((hc_ws0.mul hc_gT).aestronglyMeasurable measurableSet_Ioc) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]; filter_upwards with w hw
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hw.1, hgTrue_norm]
    have : s₀.re = 3 / 2 - 1 := by simp [s₀]; norm_num
    rw [this]
    exact le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg w]))
      (Real.rpow_nonneg hw.1.le _)) (mul_one _).le
  have hfd_int : IntegrableOn fd (Ioc (0 : ℝ) 1) :=
    (hws0_gT_int.const_mul (6 * Real.pi * Complex.I)).const_mul (hδ : ℂ)
  have hjet_rem : ‖∫ w : ℝ in Ioc (0 : ℝ) 1, (fFull w - (f0 w + ft w + ft2 w + fd w))‖ ≤
      40 * hδ ^ 2 + 10 * |ht| * |hδ| + 16 * |ht| ^ 3 := by
    let domJet : ℝ → ℝ := fun w =>
      (1 / 6) * |ht| ^ 3 * (w ^ (1 / 2 - 1 : ℝ) * (-Real.log w) ^ 3) +
      6 * Real.pi * |ht| * |hδ| * (w ^ (3 / 2 - 1 : ℝ) * (-Real.log w)) +
      2 * Real.pi ^ 2 * hδ ^ 2 * w ^ (1 / 2 - 1 : ℝ)
    have hdomJ_int : IntegrableOn domJet (Ioc (0 : ℝ) 1) :=
      ((hr3_int.const_mul _).add (hr32_1_int.const_mul _)).add (hr0_int.const_mul _)
    have hpt_jet : ∀ᵐ w ∂volume.restrict (Ioc (0 : ℝ) 1),
        ‖fFull w - (f0 w + ft w + ft2 w + fd w)‖ ≤ domJet w := by
      rw [ae_restrict_iff' measurableSet_Ioc]; filter_upwards with w hw
      have hw0 : 0 < w := hw.1
      let A : ℝ := ht * Real.log w
      let B : ℝ := 6 * Real.pi * hδ * w
      have hw_split : (w : ℂ) ^ (((1 / 2 : ℂ) + ((t₀ + ht : ℝ) : ℂ) * Complex.I) - 1) =
          (w : ℂ) ^ (s₀ - 1) * Complex.exp (Complex.I * (A : ℂ)) := by
        have hw_ne : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw0.ne'
        have hexp_ht : Complex.exp (Complex.I * (A : ℂ)) = (w : ℂ) ^ ((ht : ℂ) * Complex.I) := by
          dsimp [A]
          rw [Complex.cpow_def_of_ne_zero hw_ne, ← Complex.ofReal_log hw0.le]
          congr 1; push_cast; ring
        rw [hexp_ht, ← Complex.cpow_add _ _ hw_ne]
        congr 1; dsimp [s₀]; push_cast; ring
      have hg_split : Complex.exp (-(9 / 2 : ℂ) * (w : ℂ) ^ 2 + 6 * Real.pi * Complex.I * ((δ₀ + hδ : ℝ) : ℂ) * (w : ℂ)) =
          gTrue w * Complex.exp (Complex.I * (B : ℂ)) := by
        dsimp [gTrue, B]; rw [← Complex.exp_add]; congr 1; push_cast; ring
      have hws0_split : (w : ℂ) ^ s₀ = (w : ℂ) ^ (s₀ - 1) * (w : ℂ) := by
        have hw_ne : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw0.ne'
        conv_lhs => rw [show s₀ = (s₀ - 1) + 1 by ring, Complex.cpow_add _ _ hw_ne, Complex.cpow_one]
      have halg : fFull w - (f0 w + ft w + ft2 w + fd w) =
          (w : ℂ) ^ (s₀ - 1) * gTrue w *
            ((Complex.exp (Complex.I * (A : ℂ)) - (1 + Complex.I * (A : ℂ) - (1 / 2 : ℂ) * ((A : ℂ) * (A : ℂ)))) +
              (Complex.exp (Complex.I * (A : ℂ)) - 1) * (Complex.exp (Complex.I * (B : ℂ)) - 1) +
              (Complex.exp (Complex.I * (B : ℂ)) - (1 + Complex.I * (B : ℂ)))) := by
        dsimp only [fFull, f0, ft, ft2, fd]
        rw [hw_split, hg_split, hws0_split]
        dsimp only [A, B]
        push_cast
        ring
      rw [halg, norm_mul, norm_mul, hw_norm w hw, hgTrue_norm]
      have htri3 :
          ‖(cexp (Complex.I * ↑A) - (1 + Complex.I * ↑A - 1 / 2 * (↑A * ↑A))) +
              (cexp (Complex.I * ↑A) - 1) * (cexp (Complex.I * ↑B) - 1) +
              (cexp (Complex.I * ↑B) - (1 + Complex.I * ↑B))‖ ≤
            |A| ^ 3 / 6 + |A| * |B| + B ^ 2 / 2 := by
        refine le_trans (norm_add_le _ _) (add_le_add (le_trans (norm_add_le _ _) (add_le_add ?_ ?_)) ?_)
        · exact norm_cexp_I_sub_T2 A
        · rw [norm_mul]
          exact mul_le_mul (norm_cexp_I_sub_T0 A) (norm_cexp_I_sub_T0 B) (norm_nonneg _) (abs_nonneg _)
        · exact norm_cexp_I_sub_T1 B
      have hA_abs : |A| = |ht| * (-Real.log w) := by
        dsimp [A]; rw [abs_mul, abs_of_nonpos (Real.log_nonpos hw0.le hw.2)]
      have hB_abs : |B| = 6 * Real.pi * |hδ| * w := by
        dsimp [B]
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6),
          abs_of_pos Real.pi_pos, abs_of_pos hw0]
      have hexp1 : Real.exp (-(9 / 2) * w ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg w])
      have hb2_exp : Real.exp (-(9 / 2) * w ^ 2) * (B ^ 2 / 2) ≤ 2 * Real.pi ^ 2 * hδ ^ 2 := by
        have hxe := x_mul_exp_neg_le_half (by positivity : 0 ≤ (9 / 2 : ℝ) * w ^ 2)
        have hid : Real.exp (-(9 / 2) * w ^ 2) * (B ^ 2 / 2) =
            4 * Real.pi ^ 2 * hδ ^ 2 * ((9 / 2 * w ^ 2) * Real.exp (-((9 / 2) * w ^ 2))) := by
          dsimp [B]
          rw [show -(9 / 2) * w ^ 2 = -(9 / 2 * w ^ 2) by ring]
          ring
        rw [hid]
        have := mul_le_mul_of_nonneg_left hxe (by positivity : 0 ≤ 4 * Real.pi ^ 2 * hδ ^ 2)
        linarith only [this]
      have hwr_prod : w ^ (1 / 2 - 1 : ℝ) * w = w ^ (3 / 2 - 1 : ℝ) := by
        calc
          w ^ (1 / 2 - 1 : ℝ) * w = w ^ (1 / 2 - 1 : ℝ) * w ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = w ^ (3 / 2 - 1 : ℝ) := by rw [← Real.rpow_add hw0]; norm_num
      have hstep1 : w ^ (1 / 2 - 1 : ℝ) * Real.exp (-(9 / 2) * w ^ 2) *
            ‖(cexp (Complex.I * ↑A) - (1 + Complex.I * ↑A - 1 / 2 * (↑A * ↑A))) +
                (cexp (Complex.I * ↑A) - 1) * (cexp (Complex.I * ↑B) - 1) +
                (cexp (Complex.I * ↑B) - (1 + Complex.I * ↑B))‖ ≤
          w ^ (1 / 2 - 1 : ℝ) * Real.exp (-(9 / 2) * w ^ 2) *
            (|A| ^ 3 / 6 + |A| * |B| + B ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left htri3 (by positivity)
      refine le_trans hstep1 ?_
      dsimp [domJet]
      have ht_p1 : Real.exp (-(9 / 2) * w ^ 2) * (|A| ^ 3 / 6) ≤ (1 / 6) * |ht| ^ 3 * (-Real.log w) ^ 3 := by
        rw [hA_abs, mul_pow]
        have hnn_log3 : 0 ≤ |ht| ^ 3 * (-Real.log w) ^ 3 / 6 :=
          div_nonneg (mul_nonneg (pow_nonneg (abs_nonneg ht) 3)
            (pow_nonneg (neg_nonneg.mpr (Real.log_nonpos hw0.le hw.2)) 3)) (by norm_num)
        have := mul_le_mul_of_nonneg_right hexp1 hnn_log3
        linarith only [this]
      have ht_p2 : Real.exp (-(9 / 2) * w ^ 2) * (|A| * |B|) ≤ 6 * Real.pi * |ht| * |hδ| * (w * -Real.log w) := by
        rw [hA_abs, hB_abs]
        have := mul_le_mul_of_nonneg_right hexp1
          (mul_nonneg (mul_nonneg (abs_nonneg ht) (neg_nonneg.mpr (Real.log_nonpos hw0.le hw.2)))
            (by positivity : 0 ≤ 6 * Real.pi * |hδ| * w))
        linarith only [this]
      have hsum3 : Real.exp (-(9 / 2) * w ^ 2) * (|A| ^ 3 / 6 + |A| * |B| + B ^ 2 / 2) ≤
          (1 / 6) * |ht| ^ 3 * (-Real.log w) ^ 3 +
          6 * Real.pi * |ht| * |hδ| * (w * -Real.log w) +
          2 * Real.pi ^ 2 * hδ ^ 2 := by linarith only [ht_p1, ht_p2, hb2_exp]
      calc
        w ^ (1 / 2 - 1 : ℝ) * Real.exp (-(9 / 2) * w ^ 2) * (|A| ^ 3 / 6 + |A| * |B| + B ^ 2 / 2)
          = w ^ (1 / 2 - 1 : ℝ) * (Real.exp (-(9 / 2) * w ^ 2) * (|A| ^ 3 / 6 + |A| * |B| + B ^ 2 / 2)) := by ring
        _ ≤ w ^ (1 / 2 - 1 : ℝ) *
              ((1 / 6) * |ht| ^ 3 * (-Real.log w) ^ 3 +
               6 * Real.pi * |ht| * |hδ| * (w * -Real.log w) +
               2 * Real.pi ^ 2 * hδ ^ 2) :=
            mul_le_mul_of_nonneg_left hsum3 (Real.rpow_nonneg hw0.le _)
        _ = 1 / 6 * |ht| ^ 3 * (w ^ (1 / 2 - 1 : ℝ) * (-Real.log w) ^ 3) +
              6 * Real.pi * |ht| * |hδ| * ((w ^ (1 / 2 - 1 : ℝ) * w) * -Real.log w) +
              2 * Real.pi ^ 2 * hδ ^ 2 * w ^ (1 / 2 - 1 : ℝ) := by ring
        _ = 1 / 6 * |ht| ^ 3 * (w ^ (1 / 2 - 1 : ℝ) * (-Real.log w) ^ 3) +
              6 * Real.pi * |ht| * |hδ| * (w ^ (3 / 2 - 1 : ℝ) * -Real.log w) +
              2 * Real.pi ^ 2 * hδ ^ 2 * w ^ (1 / 2 - 1 : ℝ) := by rw [hwr_prod]
    have hcomb_int := hfFull_int.sub (((hf0_int.add hft_int).add hft2_int).add hfd_int)
    have hint_le : ‖∫ w : ℝ in Ioc (0 : ℝ) 1, (fFull w - (f0 w + ft w + ft2 w + fd w))‖ ≤ ∫ w : ℝ in Ioc (0 : ℝ) 1, domJet w :=
      le_trans (norm_integral_le_integral_norm _) (integral_mono_ae hcomb_int.norm hdomJ_int hpt_jet)
    have hdom_eval : ∫ w : ℝ in Ioc (0 : ℝ) 1, domJet w =
        16 * |ht| ^ 3 + (8 / 3) * Real.pi * |ht| * |hδ| + 4 * Real.pi ^ 2 * hδ ^ 2 := by
      have hi_a : IntegrableOn (fun w : ℝ => (1 / 6) * |ht| ^ 3 * (w ^ (1 / 2 - 1 : ℝ) * (-Real.log w) ^ 3)) (Ioc (0 : ℝ) 1) :=
        hr3_int.const_mul _
      have hi_b : IntegrableOn (fun w : ℝ => 6 * Real.pi * |ht| * |hδ| * (w ^ (3 / 2 - 1 : ℝ) * (-Real.log w))) (Ioc (0 : ℝ) 1) :=
        hr32_1_int.const_mul _
      have hi_c : IntegrableOn (fun w : ℝ => 2 * Real.pi ^ 2 * hδ ^ 2 * w ^ (1 / 2 - 1 : ℝ)) (Ioc (0 : ℝ) 1) :=
        hr0_int.const_mul _
      have hi_ab : IntegrableOn (fun w : ℝ =>
          (1 / 6) * |ht| ^ 3 * (w ^ (1 / 2 - 1 : ℝ) * (-Real.log w) ^ 3) +
          6 * Real.pi * |ht| * |hδ| * (w ^ (3 / 2 - 1 : ℝ) * (-Real.log w))) (Ioc (0 : ℝ) 1) :=
        hi_a.add hi_b
      dsimp [domJet]
      rw [integral_add hi_ab hi_c, integral_add hi_a hi_b,
        integral_const_mul, integral_const_mul, integral_const_mul,
        hr3_val, hr32_1_val, hr0_val]
      ring
    rw [hdom_eval] at hint_le
    have hpi_sq : 4 * Real.pi ^ 2 < 40 := by nlinarith only [Real.pi_pos, hpi_lt_315]
    have hpi_83 : (8 / 3 : ℝ) * Real.pi < 10 := by linarith only [hpi_lt_315]
    have h1 : 4 * Real.pi ^ 2 * hδ ^ 2 ≤ 40 * hδ ^ 2 :=
      mul_le_mul_of_nonneg_right hpi_sq.le (sq_nonneg _)
    have h2 : (8 / 3 : ℝ) * Real.pi * |ht| * |hδ| ≤ 10 * |ht| * |hδ| := by
      have := mul_le_mul_of_nonneg_right hpi_83.le (mul_nonneg (abs_nonneg ht) (abs_nonneg hδ))
      linarith only [this]
    linarith only [hint_le, h1, h2]
  have herr0 : ‖(∫ w : ℝ in Ioc (0 : ℝ) 1, f0 w) - polyJ0 ω s₀‖ ≤ 242 / 10000000 := by
    rw [← hP0_val, ← integral_sub hf0_int hP0_int]
    refine le_trans (norm_integral_le_integral_norm _) ?_
    have hpt : ∀ᵐ w ∂volume.restrict (Ioc (0 : ℝ) 1),
        ‖f0 w - (w : ℂ) ^ (s₀ - 1) * P w‖ ≤ (121 / 10000000) * w ^ (1 / 2 - 1 : ℝ) := by
      rw [ae_restrict_iff' measurableSet_Ioc]; filter_upwards with w hw
      dsimp [f0]; rw [← mul_sub, norm_mul, hw_norm w hw, mul_comm]
      exact mul_le_mul_of_nonneg_right (hg_diff w hw) (Real.rpow_nonneg hw.1.le _)
    calc
      ∫ w : ℝ in Ioc (0 : ℝ) 1, ‖f0 w - (w : ℂ) ^ (s₀ - 1) * P w‖
        ≤ ∫ w : ℝ in Ioc (0 : ℝ) 1, (121 / 10000000 : ℝ) * w ^ (1 / 2 - 1 : ℝ) :=
          integral_mono_ae (hf0_int.sub hP0_int).norm (hr0_int.const_mul _) hpt
      _ = (121 / 10000000) * ∫ w : ℝ in Ioc (0 : ℝ) 1, w ^ (1 / 2 - 1 : ℝ) := integral_const_mul _ _
      _ = 242 / 10000000 := by rw [hr0_val]; norm_num
  have herrt : ‖(∫ w : ℝ in Ioc (0 : ℝ) 1, ft w) - (ht : ℂ) * polyJt ω s₀‖ ≤ |ht| * (1 / 20000) := by
    dsimp [ft]
    rw [integral_const_mul, ← hPt_val, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hi1 : IntegrableOn (fun w : ℝ => Complex.I * ↑(Real.log w) * ↑w ^ (s₀ - 1) * gTrue w) (Ioc (0 : ℝ) 1) := by
      refine hr1_int.mono'
        ((((continuousOn_const.mul hc_log).mul hc_wp).mul hc_gT).aestronglyMeasurable measurableSet_Ioc) ?_
      rw [ae_restrict_iff' measurableSet_Ioc]; filter_upwards with w hw
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (Real.log_nonpos hw.1.le hw.2), hw_norm w hw, hgTrue_norm]
      have hexp1 : Real.exp (-(9 / 2) * w ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg w])
      calc
        -Real.log w * w ^ (1 / 2 - 1 : ℝ) * Real.exp (-(9 / 2) * w ^ 2)
          ≤ -Real.log w * w ^ (1 / 2 - 1 : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hexp1
              (mul_nonneg (neg_nonneg.mpr (Real.log_nonpos hw.1.le hw.2)) (Real.rpow_nonneg hw.1.le _))
        _ = w ^ (1 / 2 - 1 : ℝ) * -Real.log w := by ring
    have hsub_eq : (∫ w : ℝ in Ioc (0 : ℝ) 1, Complex.I * ↑(Real.log w) * ↑w ^ (s₀ - 1) * gTrue w) -
        (∫ w : ℝ in Ioc (0 : ℝ) 1, Complex.I * ↑(Real.log w) * ↑w ^ (s₀ - 1) * P w) =
        ∫ w : ℝ in Ioc (0 : ℝ) 1, (Complex.I * ↑(Real.log w) * ↑w ^ (s₀ - 1) * (gTrue w - P w)) := by
      rw [← integral_sub hi1 hPt_int]
      exact setIntegral_congr_fun measurableSet_Ioc fun w _ => by ring
    rw [hsub_eq]
    have hpt : ∀ᵐ w ∂volume.restrict (Ioc (0 : ℝ) 1),
        ‖Complex.I * (Real.log w : ℂ) * (w : ℂ) ^ (s₀ - 1) * (gTrue w - P w)‖ ≤
          (121 / 10000000) * (w ^ (1 / 2 - 1 : ℝ) * (-Real.log w)) := by
      rw [ae_restrict_iff' measurableSet_Ioc]; filter_upwards with w hw
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (Real.log_nonpos hw.1.le hw.2), hw_norm w hw]
      have hmul := mul_le_mul_of_nonneg_left (hg_diff w hw)
        (mul_nonneg (neg_nonneg.mpr (Real.log_nonpos hw.1.le hw.2)) (Real.rpow_nonneg hw.1.le (1 / 2 - 1 : ℝ)))
      linarith only [hmul]
    calc
      ‖∫ w : ℝ in Ioc (0 : ℝ) 1, Complex.I * ↑(Real.log w) * ↑w ^ (s₀ - 1) * (gTrue w - P w)‖
        ≤ ∫ w : ℝ in Ioc (0 : ℝ) 1, (121 / 10000000 : ℝ) * (w ^ (1 / 2 - 1 : ℝ) * (-Real.log w)) :=
          le_trans (norm_integral_le_integral_norm _)
            (integral_mono_ae ((hi1.sub hPt_int).congr_fun (fun w _ => by
              change Complex.I * ↑(Real.log w) * ↑w ^ (s₀ - 1) * gTrue w -
                Complex.I * ↑(Real.log w) * ↑w ^ (s₀ - 1) * P w = _
              ring) measurableSet_Ioc).norm
              (hr1_int.const_mul _) hpt)
      _ = (121 / 10000000) * ∫ w : ℝ in Ioc (0 : ℝ) 1, w ^ (1 / 2 - 1 : ℝ) * (-Real.log w) := integral_const_mul _ _
      _ ≤ 1 / 20000 := by rw [hr1_val]; norm_num
  have herrt2 : ‖(∫ w : ℝ in Ioc (0 : ℝ) 1, ft2 w) - ((ht ^ 2 : ℝ) : ℂ) * polyJt2 ω s₀‖ ≤ ht ^ 2 * (1 / 10000) := by
    dsimp [ft2]
    rw [integral_const_mul, ← hPt2_val, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ht)]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have hi2 : IntegrableOn (fun w : ℝ => -(1 / 2 : ℂ) * ((Real.log w : ℂ) * (Real.log w : ℂ)) * (w : ℂ) ^ (s₀ - 1) * gTrue w) (Ioc (0 : ℝ) 1) := by
      refine (hr2_int.const_mul (1 / 2)).mono'
        ((((continuousOn_const.mul (hc_log.mul hc_log)).mul hc_wp).mul hc_gT).aestronglyMeasurable measurableSet_Ioc) ?_
      rw [ae_restrict_iff' measurableSet_Ioc]; filter_upwards with w hw
      rw [norm_mul, norm_mul, norm_mul, norm_neg, norm_div, norm_one, Complex.norm_ofNat,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, hw_norm w hw, hgTrue_norm]
      have hexp1 : Real.exp (-(9 / 2) * w ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg w])
      have hll : |Real.log w| * |Real.log w| = (Real.log w) ^ 2 := by
        rw [← abs_mul, abs_of_nonneg (mul_self_nonneg _)]; ring
      rw [hll]
      calc
        1 / 2 * (Real.log w) ^ 2 * w ^ (1 / 2 - 1 : ℝ) * Real.exp (-(9 / 2) * w ^ 2)
          ≤ 1 / 2 * (Real.log w) ^ 2 * w ^ (1 / 2 - 1 : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hexp1
              (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (Real.rpow_nonneg hw.1.le _))
        _ = 1 / 2 * (w ^ (1 / 2 - 1 : ℝ) * (Real.log w) ^ 2) := by ring
    have hsub_eq : (∫ w : ℝ in Ioc (0 : ℝ) 1, -(1 / 2 : ℂ) * (↑(Real.log w) * ↑(Real.log w)) * ↑w ^ (s₀ - 1) * gTrue w) -
        (∫ w : ℝ in Ioc (0 : ℝ) 1, -(1 / 2 : ℂ) * (↑(Real.log w) * ↑(Real.log w)) * ↑w ^ (s₀ - 1) * P w) =
        ∫ w : ℝ in Ioc (0 : ℝ) 1, (-(1 / 2 : ℂ) * (↑(Real.log w) * ↑(Real.log w)) * ↑w ^ (s₀ - 1) * (gTrue w - P w)) := by
      rw [← integral_sub hi2 hPt2_int]
      exact setIntegral_congr_fun measurableSet_Ioc fun w _ => by
        change -(1 / 2 : ℂ) * (↑(Real.log w) * ↑(Real.log w)) * ↑w ^ (s₀ - 1) * gTrue w -
          -(1 / 2 : ℂ) * (↑(Real.log w) * ↑(Real.log w)) * ↑w ^ (s₀ - 1) * P w = _
        ring
    rw [hsub_eq]
    have hpt : ∀ᵐ w ∂volume.restrict (Ioc (0 : ℝ) 1),
        ‖-(1 / 2 : ℂ) * ((Real.log w : ℂ) * (Real.log w : ℂ)) * (w : ℂ) ^ (s₀ - 1) * (gTrue w - P w)‖ ≤
          ((1 / 2) * (121 / 10000000)) * (w ^ (1 / 2 - 1 : ℝ) * (Real.log w) ^ 2) := by
      rw [ae_restrict_iff' measurableSet_Ioc]; filter_upwards with w hw
      rw [norm_mul, norm_mul, norm_mul, norm_neg, norm_div, norm_one, Complex.norm_ofNat,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, hw_norm w hw]
      have hll : |Real.log w| * |Real.log w| = (Real.log w) ^ 2 := by
        rw [← abs_mul, abs_of_nonneg (mul_self_nonneg _)]; ring
      rw [hll]
      have hmul := mul_le_mul_of_nonneg_left (hg_diff w hw)
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (sq_nonneg (Real.log w)))
          (Real.rpow_nonneg hw.1.le (1 / 2 - 1 : ℝ)))
      linarith only [hmul]
    calc
      ‖∫ w : ℝ in Ioc (0 : ℝ) 1, -(1 / 2 : ℂ) * (↑(Real.log w) * ↑(Real.log w)) * ↑w ^ (s₀ - 1) * (gTrue w - P w)‖
        ≤ ∫ w : ℝ in Ioc (0 : ℝ) 1, ((1 / 2) * (121 / 10000000) : ℝ) * (w ^ (1 / 2 - 1 : ℝ) * (Real.log w) ^ 2) :=
          le_trans (norm_integral_le_integral_norm _)
            (integral_mono_ae ((hi2.sub hPt2_int).congr_fun (fun w _ => by
              change -(1 / 2 : ℂ) * (↑(Real.log w) * ↑(Real.log w)) * ↑w ^ (s₀ - 1) * gTrue w -
                -(1 / 2 : ℂ) * (↑(Real.log w) * ↑(Real.log w)) * ↑w ^ (s₀ - 1) * P w = _
              ring) measurableSet_Ioc).norm
              (hr2_int.const_mul _) hpt)
      _ = ((1 / 2) * (121 / 10000000)) * ∫ w : ℝ in Ioc (0 : ℝ) 1, w ^ (1 / 2 - 1 : ℝ) * (Real.log w) ^ 2 := integral_const_mul _ _
      _ ≤ 1 / 10000 := by rw [hr2_val]; norm_num
  have herrd : ‖∫ w : ℝ in Ioc (0 : ℝ) 1, fd w‖ ≤ |hδ| * ((6 * pi0R) * ‖polyJdRaw ω s₀‖ + 1 / 6000) := by
    have hfd_norm : ‖∫ w : ℝ in Ioc (0 : ℝ) 1, fd w‖ =
        |hδ| * (6 * Real.pi * ‖∫ w : ℝ in Ioc (0 : ℝ) 1, (w : ℂ) ^ s₀ * gTrue w‖) := by
      dsimp [fd]
      have h6i : (6 : ℂ) * ↑Real.pi * Complex.I = ((6 * Real.pi : ℝ) : ℂ) * Complex.I := by push_cast; rfl
      simp_rw [h6i]
      rw [integral_const_mul, integral_const_mul, norm_mul, norm_mul, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (mul_pos (by norm_num) Real.pi_pos), Complex.norm_I, mul_one]
    rw [hfd_norm]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hdiff_d : ‖(∫ w : ℝ in Ioc (0 : ℝ) 1, (w : ℂ) ^ s₀ * gTrue w) - polyJdRaw ω s₀‖ ≤ (2 / 3) * (121 / 10000000) := by
      rw [← hPd_val, ← integral_sub hws0_gT_int hPd_int]
      have hpt : ∀ᵐ (w : ℝ) ∂volume.restrict (Ioc (0 : ℝ) 1),
          ‖(w : ℂ) ^ s₀ * gTrue w - (w : ℂ) ^ s₀ * P w‖ ≤ (121 / 10000000) * w ^ (3 / 2 - 1 : ℝ) := by
        rw [ae_restrict_iff' measurableSet_Ioc]; filter_upwards with w hw
        rw [← mul_sub, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hw.1, mul_comm]
        have : s₀.re = 3 / 2 - 1 := by simp [s₀]; norm_num
        rw [this]
        exact mul_le_mul_of_nonneg_right (hg_diff w hw) (Real.rpow_nonneg hw.1.le _)
      calc
        ‖∫ w : ℝ in Ioc (0 : ℝ) 1, ((w : ℂ) ^ s₀ * gTrue w - (w : ℂ) ^ s₀ * P w)‖
          ≤ ∫ w : ℝ in Ioc (0 : ℝ) 1, (121 / 10000000 : ℝ) * w ^ (3 / 2 - 1 : ℝ) :=
            le_trans (norm_integral_le_integral_norm _)
              (integral_mono_ae (hws0_gT_int.sub hPd_int).norm (hr32_0_int.const_mul _) hpt)
        _ = (121 / 10000000) * ∫ w : ℝ in Ioc (0 : ℝ) 1, w ^ (3 / 2 - 1 : ℝ) := integral_const_mul _ _
        _ = (2 / 3) * (121 / 10000000) := by rw [hr32_0_val]; norm_num
    have htri_d : ‖∫ w : ℝ in Ioc (0 : ℝ) 1, (w : ℂ) ^ s₀ * gTrue w‖ ≤ ‖polyJdRaw ω s₀‖ + (2 / 3) * (121 / 10000000) := by
      have := norm_sub_norm_le (∫ w : ℝ in Ioc (0 : ℝ) 1, (w : ℂ) ^ s₀ * gTrue w) (polyJdRaw ω s₀)
      linarith only [this, hdiff_d]
    have h6pi_le : 6 * Real.pi * ‖polyJdRaw ω s₀‖ ≤ (6 * pi0R) * ‖polyJdRaw ω s₀‖ :=
      mul_le_mul_of_nonneg_right (by linarith only [hpi_le_pi0]) (norm_nonneg _)
    have h6pi_err : 6 * Real.pi * ((2 / 3) * (121 / 10000000)) ≤ 1 / 6000 := by
      linarith only [hpi_lt_315]
    have h6pi_tri := mul_le_mul_of_nonneg_left htri_d (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) Real.pi_pos.le)
    linarith only [h6pi_tri, h6pi_le, h6pi_err]
  have hG3_decomp : G3 (δ₀ + hδ) (t₀ + ht) =
      (∫ w : ℝ in Ioc (0 : ℝ) 1, (fFull w - (f0 w + ft w + ft2 w + fd w))) +
      (∫ w : ℝ in Ioc (0 : ℝ) 1, f0 w) + (∫ w : ℝ in Ioc (0 : ℝ) 1, ft w) +
      (∫ w : ℝ in Ioc (0 : ℝ) 1, ft2 w) + (∫ w : ℝ in Ioc (0 : ℝ) 1, fd w) := by
    have h01 : IntegrableOn (fun w => f0 w + ft w) (Ioc (0 : ℝ) 1) := hf0_int.add hft_int
    have h012 : IntegrableOn (fun w => f0 w + ft w + ft2 w) (Ioc (0 : ℝ) 1) := h01.add hft2_int
    have hsum_int : IntegrableOn (fun w => f0 w + ft w + ft2 w + fd w) (Ioc (0 : ℝ) 1) := h012.add hfd_int
    have hrem_int : IntegrableOn (fun w => fFull w - (f0 w + ft w + ft2 w + fd w)) (Ioc (0 : ℝ) 1) :=
      hfFull_int.sub hsum_int
    have h1 := integral_add hrem_int hsum_int
    have h2 : ∫ w : ℝ in Ioc (0 : ℝ) 1, ((fun u => fFull u - (f0 u + ft u + ft2 u + fd u)) w +
        (fun u => f0 u + ft u + ft2 u + fd u) w) = G3 (δ₀ + hδ) (t₀ + ht) := by
      dsimp [G3, fFull]
      exact setIntegral_congr_fun measurableSet_Ioc fun w _ => by ring
    rw [h2] at h1
    rw [h1, integral_add h012 hfd_int, integral_add h01 hft2_int, integral_add hf0_int hft_int]
    ring
  rw [hG3_decomp]
  have hsplit5 :
      (∫ w : ℝ in Ioc (0 : ℝ) 1, (fFull w - (f0 w + ft w + ft2 w + fd w))) +
        (∫ w : ℝ in Ioc (0 : ℝ) 1, f0 w) + (∫ w : ℝ in Ioc (0 : ℝ) 1, ft w) +
        (∫ w : ℝ in Ioc (0 : ℝ) 1, ft2 w) + (∫ w : ℝ in Ioc (0 : ℝ) 1, fd w) -
        (polyJ0 ω s₀ + (ht : ℂ) * polyJt ω s₀ + ((ht ^ 2 : ℝ) : ℂ) * polyJt2 ω s₀) =
      (∫ w : ℝ in Ioc (0 : ℝ) 1, (fFull w - (f0 w + ft w + ft2 w + fd w))) +
      ((∫ w : ℝ in Ioc (0 : ℝ) 1, f0 w) - polyJ0 ω s₀) +
      ((∫ w : ℝ in Ioc (0 : ℝ) 1, ft w) - (ht : ℂ) * polyJt ω s₀) +
      ((∫ w : ℝ in Ioc (0 : ℝ) 1, ft2 w) - ((ht ^ 2 : ℝ) : ℂ) * polyJt2 ω s₀) +
      (∫ w : ℝ in Ioc (0 : ℝ) 1, fd w) := by ring
  rw [hsplit5]
  have ht1 := norm_add_le
    ((∫ w : ℝ in Ioc (0 : ℝ) 1, (fFull w - (f0 w + ft w + ft2 w + fd w))) +
      ((∫ w : ℝ in Ioc (0 : ℝ) 1, f0 w) - polyJ0 ω s₀) +
      ((∫ w : ℝ in Ioc (0 : ℝ) 1, ft w) - (ht : ℂ) * polyJt ω s₀) +
      ((∫ w : ℝ in Ioc (0 : ℝ) 1, ft2 w) - ((ht ^ 2 : ℝ) : ℂ) * polyJt2 ω s₀))
    (∫ w : ℝ in Ioc (0 : ℝ) 1, fd w)
  have ht2 := norm_add_le
    ((∫ w : ℝ in Ioc (0 : ℝ) 1, (fFull w - (f0 w + ft w + ft2 w + fd w))) +
      ((∫ w : ℝ in Ioc (0 : ℝ) 1, f0 w) - polyJ0 ω s₀) +
      ((∫ w : ℝ in Ioc (0 : ℝ) 1, ft w) - (ht : ℂ) * polyJt ω s₀))
    ((∫ w : ℝ in Ioc (0 : ℝ) 1, ft2 w) - ((ht ^ 2 : ℝ) : ℂ) * polyJt2 ω s₀)
  have ht3 := norm_add_le
    ((∫ w : ℝ in Ioc (0 : ℝ) 1, (fFull w - (f0 w + ft w + ft2 w + fd w))) +
      ((∫ w : ℝ in Ioc (0 : ℝ) 1, f0 w) - polyJ0 ω s₀))
    ((∫ w : ℝ in Ioc (0 : ℝ) 1, ft w) - (ht : ℂ) * polyJt ω s₀)
  have ht4 := norm_add_le
    (∫ w : ℝ in Ioc (0 : ℝ) 1, (fFull w - (f0 w + ft w + ft2 w + fd w)))
    ((∫ w : ℝ in Ioc (0 : ℝ) 1, f0 w) - polyJ0 ω s₀)
  linarith only [ht1, ht2, ht3, ht4, hjet_rem, herr0, herrt, herrt2, herrd]

lemma mellin_num_jet_le {δ₀ : ℝ} (hδ₀ : |δ₀| ≤ 1) (hδ t₀ ht : ℝ) :
    let ω : ℝ := 6 * pi0R * δ₀
    let s₀ : ℂ := (1 / 2 : ℂ) + (t₀ : ℝ) * Complex.I
    ‖mellinVal (δ₀ + hδ) ((1 / 2 : ℂ) + ((t₀ + ht : ℝ) : ℂ) * Complex.I)‖ ≤
      Real.sqrt 3 * (
        ‖polyJ0 ω s₀ + (ht : ℂ) * polyJt ω s₀ + ((ht ^ 2 : ℝ) : ℂ) * polyJt2 ω s₀‖ +
        (1 / 780 : ℝ) +
        |hδ| * ((6 * pi0R) * ‖polyJdRaw ω s₀‖ + (1 / 6000 : ℝ)) +
        |ht| * (1 / 20000 : ℝ) +
        ht ^ 2 * (1 / 10000 : ℝ) +
        40 * hδ ^ 2 + 10 * |ht| * |hδ| + 16 * |ht| ^ 3) := by
  intro ω s₀
  obtain ⟨hup, _⟩ := mellinVal_split_G3 (δ₀ + hδ) (t₀ + ht)
  have hjet := G3_jet_approx hδ₀ hδ t₀ ht
  have htri := norm_sub_norm_le (G3 (δ₀ + hδ) (t₀ + ht))
    (polyJ0 ω s₀ + (ht : ℂ) * polyJt ω s₀ + ((ht ^ 2 : ℝ) : ℂ) * polyJt2 ω s₀)
  have h780 : (242 / 10000000 : ℝ) + 1 / 801 ≤ 1 / 780 := by norm_num
  have hG_le : ‖G3 (δ₀ + hδ) (t₀ + ht)‖ + 1 / 801 ≤
      ‖polyJ0 ω s₀ + (ht : ℂ) * polyJt ω s₀ + ((ht ^ 2 : ℝ) : ℂ) * polyJt2 ω s₀‖ +
      (1 / 780 : ℝ) +
      |hδ| * ((6 * pi0R) * ‖polyJdRaw ω s₀‖ + (1 / 6000 : ℝ)) +
      |ht| * (1 / 20000 : ℝ) +
      ht ^ 2 * (1 / 10000 : ℝ) +
      40 * hδ ^ 2 + 10 * |ht| * |hδ| + 16 * |ht| ^ 3 := by linarith
  exact le_trans hup (mul_le_mul_of_nonneg_left hG_le (Real.sqrt_nonneg 3))

lemma mellin_den_jet_ge {δ₀ : ℝ} (hδ₀ : |δ₀| ≤ 1) (hδ : ℝ) :
    let ω : ℝ := 6 * pi0R * δ₀
    let sm1 : ℂ := (1 / 2 : ℂ) - Complex.I
    Real.sqrt 3 * (
      ‖polyJ0 ω sm1‖ - (
        (1 / 780 : ℝ) +
        |hδ| * ((6 * pi0R) * ‖polyJdRaw ω sm1‖ + (1 / 6000 : ℝ)) +
        40 * hδ ^ 2)) ≤
      ‖mellinVal (δ₀ + hδ) sm1‖ := by
  intro ω sm1
  have hsm1 : sm1 = (1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I := by dsimp [sm1]; push_cast; ring
  rw [hsm1]
  obtain ⟨_, hlo⟩ := mellinVal_split_G3 (δ₀ + hδ) (-1)
  have hjet := G3_jet_approx hδ₀ hδ (-1) 0
  simp only [add_zero, Complex.ofReal_zero, zero_mul, abs_zero, mul_zero, zero_pow (by norm_num : 2 ≠ 0),
    zero_pow (by norm_num : 3 ≠ 0)] at hjet
  have htri := norm_sub_norm_le (polyJ0 ω ((1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I)) (G3 (δ₀ + hδ) (-1))
  rw [norm_sub_rev] at htri
  have h780 : (242 / 10000000 : ℝ) + 1 / 801 ≤ 1 / 780 := by norm_num
  have hG_ge : ‖polyJ0 ω ((1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I)‖ -
      ((1 / 780 : ℝ) + |hδ| * ((6 * pi0R) * ‖polyJdRaw ω ((1 / 2 : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I)‖ + (1 / 6000 : ℝ)) +
        40 * hδ ^ 2) ≤ ‖G3 (δ₀ + hδ) (-1)‖ - 1 / 801 := by linarith
  exact le_trans (mul_le_mul_of_nonneg_left hG_ge (Real.sqrt_nonneg 3)) hlo

end GaussSmallBridge
end


open Real Complex MeasureTheory Filter Set
open scoped BigOperators

namespace GaussSmallBridge

/-! ### Part 4B-1: Checker Data Structures, Offset-`Nat` Arithmetic, `checkBTree`, and `sumBTree` -/

inductive BTree where
  | L (v : Nat)
  | N (l r : BTree)

inductive QTree where
  | Q (up udp uvt2 : Nat)
  | Z (l r : QTree)
  | S (l r : QTree)

inductive StripCert where
  | M (v0r v0i vdr vdi vtr vti vt2r vt2i udMSum : Nat) (qt : QTree)

inductive FastDTree where
  | dleaf (bt : BTree) (dv0r dv0i dvdr dvdi lDen udDenSum : Nat)
      (s17 s19 s21 s23 : StripCert)
  | dsplit (l r : FastDTree)

def onatMulDiv (z u : Nat) (neg : Bool) (num den : Nat) : Nat :=
  if Nat.ble z u then
    let mag := Nat.div (Nat.mul (Nat.sub u z) num) den
    if neg then Nat.sub z mag else Nat.add z mag
  else
    let mag := Nat.div (Nat.mul (Nat.sub z u) num) den
    if neg then Nat.add z mag else Nat.sub z mag

def onatAdd (z a b : Nat) : Nat :=
  Nat.sub (Nat.add a b) z

def onatAbs (z u : Nat) : Nat :=
  if Nat.ble z u then Nat.sub u z else Nat.sub z u

def btreeGet : BTree → Nat → Nat → Nat → Nat
  | .L v, _, _, _ => v
  | .N l r, lo, hi, idx =>
    let mid := Nat.div (Nat.add lo hi) 2
    if Nat.ble mid idx then btreeGet r mid hi idx else btreeGet l lo mid idx

def checkBShape : BTree → Nat → Nat → Bool
  | .L _, lo, hi => Nat.beq (Nat.add lo 1) hi
  | .N l r, lo, hi =>
    let mid := Nat.div (Nat.add lo hi) 2
    Bool.and (Nat.ble (Nat.add lo 1) mid)
      (Bool.and (Nat.ble (Nat.add mid 1) hi)
        (Bool.and (checkBShape l lo mid) (checkBShape r mid hi)))

def checkBStep (z denBase numW : Nat) (dNeg : Bool) (bt : BTree) (n : Nat) : Bool :=
  let bPrev := btreeGet bt 0 96 (Nat.sub n 1)
  let bCurr := btreeGet bt 0 96 n
  let bNext := btreeGet bt 0 96 (Nat.add n 1)
  let n1 := Nat.add n 1
  let t1 := onatMulDiv z bCurr dNeg numW (Nat.mul denBase n1)
  let t2 := onatMulDiv z bPrev false 9 n1
  Nat.beq bNext (onatAdd z t1 t2)

def checkBLoop (z denBase numW : Nat) (dNeg : Bool) (bt : BTree) : Nat → Nat → Bool
  | 0, _ => true
  | k + 1, n =>
    Bool.and (checkBStep z denBase numW dNeg bt n)
      (checkBLoop z denBase numW dNeg bt k (Nat.add n 1))

def checkBTree (s z denBase numW : Nat) (dNeg : Bool) (bt : BTree) : Bool :=
  let expB0 := Nat.add z s
  let expB1 := onatMulDiv z expB0 dNeg numW denBase
  Bool.and (checkBShape bt 0 96)
    (Bool.and (Nat.beq (btreeGet bt 0 96 0) expB0)
      (Bool.and (Nat.beq (btreeGet bt 0 96 1) expB1)
        (checkBLoop z denBase numW dNeg bt 94 1)))

def term0R (z p P fourP2 : Nat) (bn n : Nat) : Nat :=
  let r4 := Nat.mod n 4
  let cNeg := Nat.ble 2 r4
  let cOdd := Nat.beq (Nat.mod r4 2) 1
  let u := Nat.mul (Nat.add (Nat.mul 2 n) 1) P
  let D := Nat.add (Nat.mul u u) fourP2
  if cOdd then onatMulDiv z bn (Bool.not cNeg) (Nat.mul (Nat.mul 4 P) p) D
  else onatMulDiv z bn cNeg (Nat.mul (Nat.mul 2 P) u) D

def term0I (z p P fourP2 : Nat) (bn n : Nat) : Nat :=
  let r4 := Nat.mod n 4
  let cNeg := Nat.ble 2 r4
  let cOdd := Nat.beq (Nat.mod r4 2) 1
  let u := Nat.mul (Nat.add (Nat.mul 2 n) 1) P
  let D := Nat.add (Nat.mul u u) fourP2
  if cOdd then onatMulDiv z bn cNeg (Nat.mul (Nat.mul 2 P) u) D
  else onatMulDiv z bn cNeg (Nat.mul (Nat.mul 4 P) p) D

def termDR (z p P fourP2 : Nat) (bn n : Nat) : Nat :=
  let r4 := Nat.mod n 4
  let cNeg := Nat.ble 2 r4
  let cOdd := Nat.beq (Nat.mod r4 2) 1
  let u1 := Nat.mul (Nat.add (Nat.mul 2 n) 3) P
  let D1 := Nat.add (Nat.mul u1 u1) fourP2
  if cOdd then onatMulDiv z bn (Bool.not cNeg) (Nat.mul (Nat.mul 4 P) p) D1
  else onatMulDiv z bn cNeg (Nat.mul (Nat.mul 2 P) u1) D1

def termDI (z p P fourP2 : Nat) (bn n : Nat) : Nat :=
  let r4 := Nat.mod n 4
  let cNeg := Nat.ble 2 r4
  let cOdd := Nat.beq (Nat.mod r4 2) 1
  let u1 := Nat.mul (Nat.add (Nat.mul 2 n) 3) P
  let D1 := Nat.add (Nat.mul u1 u1) fourP2
  if cOdd then onatMulDiv z bn cNeg (Nat.mul (Nat.mul 2 P) u1) D1
  else onatMulDiv z bn cNeg (Nat.mul (Nat.mul 4 P) p) D1

def termTR (z p P fourP2 fourCapP2 : Nat) (bn n : Nat) : Nat :=
  let r4 := Nat.mod n 4
  let cNeg := Nat.ble 2 r4
  let cOdd := Nat.beq (Nat.mod r4 2) 1
  let u := Nat.mul (Nat.add (Nat.mul 2 n) 1) P
  let uSq := Nat.mul u u
  let D := Nat.add uSq fourP2
  let D2 := Nat.mul D D
  if cOdd then
    let a2Neg := Bool.not (Nat.ble fourP2 uSq)
    let a2Mag := if a2Neg then Nat.mul fourCapP2 (Nat.sub fourP2 uSq) else Nat.mul fourCapP2 (Nat.sub uSq fourP2)
    onatMulDiv z bn (Bool.xor cNeg a2Neg) a2Mag D2
  else
    let b2Mag := Nat.mul (Nat.mul 16 (Nat.mul P P)) (Nat.mul u p)
    onatMulDiv z bn cNeg b2Mag D2

def termTI (z p P fourP2 fourCapP2 : Nat) (bn n : Nat) : Nat :=
  let r4 := Nat.mod n 4
  let cNeg := Nat.ble 2 r4
  let cOdd := Nat.beq (Nat.mod r4 2) 1
  let u := Nat.mul (Nat.add (Nat.mul 2 n) 1) P
  let uSq := Nat.mul u u
  let D := Nat.add uSq fourP2
  let D2 := Nat.mul D D
  if cOdd then
    let b2Mag := Nat.mul (Nat.mul 16 (Nat.mul P P)) (Nat.mul u p)
    onatMulDiv z bn cNeg b2Mag D2
  else
    let a2Neg := Bool.not (Nat.ble fourP2 uSq)
    let a2Mag := if a2Neg then Nat.mul fourCapP2 (Nat.sub fourP2 uSq) else Nat.mul fourCapP2 (Nat.sub uSq fourP2)
    onatMulDiv z bn (Bool.xor cNeg (Bool.not a2Neg)) a2Mag D2

def termT2R (z p P fourP2 eightCapP3 : Nat) (bn n : Nat) : Nat :=
  let r4 := Nat.mod n 4
  let nc := Bool.not (Nat.ble 2 r4)
  let cOdd := Nat.beq (Nat.mod r4 2) 1
  let u := Nat.mul (Nat.add (Nat.mul 2 n) 1) P
  let uSq := Nat.mul u u
  let D := Nat.add uSq fourP2
  let D3 := Nat.mul (Nat.mul D D) D
  if cOdd then
    let im3Pos := Nat.mul (Nat.mul 6 uSq) p
    let im3NegP := Nat.mul 8 (Nat.mul p (Nat.mul p p))
    let b3Neg := Bool.not (Nat.ble im3NegP im3Pos)
    let b3Mag := if b3Neg then Nat.mul eightCapP3 (Nat.sub im3NegP im3Pos) else Nat.mul eightCapP3 (Nat.sub im3Pos im3NegP)
    onatMulDiv z bn (Bool.xor (Bool.not nc) b3Neg) b3Mag D3
  else
    let re3Pos := Nat.mul u uSq
    let re3NegP := Nat.mul (Nat.mul 3 u) fourP2
    let a3Neg := Bool.not (Nat.ble re3NegP re3Pos)
    let a3Mag := if a3Neg then Nat.mul eightCapP3 (Nat.sub re3NegP re3Pos) else Nat.mul eightCapP3 (Nat.sub re3Pos re3NegP)
    onatMulDiv z bn (Bool.xor nc a3Neg) a3Mag D3

def termT2I (z p P fourP2 eightCapP3 : Nat) (bn n : Nat) : Nat :=
  let r4 := Nat.mod n 4
  let nc := Bool.not (Nat.ble 2 r4)
  let cOdd := Nat.beq (Nat.mod r4 2) 1
  let u := Nat.mul (Nat.add (Nat.mul 2 n) 1) P
  let uSq := Nat.mul u u
  let D := Nat.add uSq fourP2
  let D3 := Nat.mul (Nat.mul D D) D
  if cOdd then
    let re3Pos := Nat.mul u uSq
    let re3NegP := Nat.mul (Nat.mul 3 u) fourP2
    let a3Neg := Bool.not (Nat.ble re3NegP re3Pos)
    let a3Mag := if a3Neg then Nat.mul eightCapP3 (Nat.sub re3NegP re3Pos) else Nat.mul eightCapP3 (Nat.sub re3Pos re3NegP)
    onatMulDiv z bn (Bool.xor nc a3Neg) a3Mag D3
  else
    let im3Pos := Nat.mul (Nat.mul 6 uSq) p
    let im3NegP := Nat.mul 8 (Nat.mul p (Nat.mul p p))
    let b3Neg := Bool.not (Nat.ble im3NegP im3Pos)
    let b3Mag := if b3Neg then Nat.mul eightCapP3 (Nat.sub im3NegP im3Pos) else Nat.mul eightCapP3 (Nat.sub im3Pos im3NegP)
    onatMulDiv z bn (Bool.xor nc b3Neg) b3Mag D3

def sumBTree (z : Nat) (termFn : Nat → Nat → Nat) : BTree → Nat → Nat → Nat
  | .L bn, lo, _ => termFn bn lo
  | .N l r, lo, hi =>
    let mid := Nat.div (Nat.add lo hi) 2
    onatAdd z (sumBTree z termFn l lo mid) (sumBTree z termFn r mid hi)

noncomputable section

def valZ (z u : ℕ) : ℝ := (u : ℝ) - (z : ℝ)

def signB (b : Bool) : ℝ := if b then -1 else 1

lemma abs_signB (b : Bool) : |signB b| = 1 := by
  cases b <;> simp [signB]

lemma signB_xor (a b : Bool) : signB (Bool.xor a b) = signB a * signB b := by
  cases a <;> cases b <;> simp [signB]

lemma signB_not (a : Bool) : signB (Bool.not a) = -signB a := by
  cases a <;> simp [signB]

lemma nat_div_def (a b : ℕ) : Nat.div a b = a / b := rfl

lemma abs_le_abs_add_err (a b : ℝ) : |a| ≤ |b| + |a - b| := by
  have := abs_add_le b (a - b)
  rwa [add_sub_cancel] at this

lemma abs_ge_abs_sub_err (a b : ℝ) : |b| - |b - a| ≤ |a| := by
  have := abs_add_le a (b - a)
  rw [add_sub_cancel] at this
  linarith

lemma onatAbs_eq_abs (z u : ℕ) : (onatAbs z u : ℝ) = |valZ z u| := by
  unfold onatAbs valZ
  simp only [Nat.sub_eq]
  by_cases h : z ≤ u
  · have hb : Nat.ble z u = true := Nat.ble_eq.mpr h
    rw [hb, if_pos rfl, Nat.cast_sub h, abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h))]
  · have hb : Nat.ble z u = false := Bool.eq_false_iff.mpr fun ht => h (Nat.ble_eq.mp ht)
    have hlt : u ≤ z := le_of_not_ge h
    rw [hb, if_neg Bool.false_ne_true, Nat.cast_sub hlt,
      abs_of_nonpos (sub_nonpos.mpr (Nat.cast_le.mpr hlt))]
    ring

lemma valZ_onatAdd {z a b : ℕ} (ha : -(z : ℝ) / 2 ≤ valZ z a) (hb : -(z : ℝ) / 2 ≤ valZ z b) :
    valZ z (onatAdd z a b) = valZ z a + valZ z b := by
  unfold valZ onatAdd at *
  simp only [Nat.add_eq, Nat.sub_eq]
  have hz_le : z ≤ a + b := by
    have hr : (z : ℝ) ≤ ((a + b : ℕ) : ℝ) := by push_cast; linarith
    exact Nat.cast_le.mp hr
  rw [Nat.cast_sub hz_le, Nat.cast_add]
  ring

lemma valZ_onatMulDiv_approx {z u num den : ℕ} (neg : Bool) (hden : 0 < den)
    (hmag : |valZ z u| * (num : ℝ) / (den : ℝ) ≤ (z : ℝ)) :
    |valZ z (onatMulDiv z u neg num den) - signB neg * valZ z u * (num : ℝ) / (den : ℝ)| ≤ 1 ∧
    |valZ z (onatMulDiv z u neg num den)| ≤ |valZ z u| * (num : ℝ) / (den : ℝ) := by
  have hdenR : (0 : ℝ) < (den : ℝ) := Nat.cast_pos.mpr hden
  have helper_div : ∀ (d : ℕ), (d : ℝ) = |valZ z u| →
      ((d * num) / den ≤ z ∧
       (((d * num) / den : ℕ) : ℝ) ≤ |valZ z u| * (num : ℝ) / (den : ℝ) ∧
       |valZ z u| * (num : ℝ) / (den : ℝ) - 1 ≤ (((d * num) / den : ℕ) : ℝ)) := by
    intro d hd
    set m := (d * num) / den
    have hm_mul : (m : ℝ) * (den : ℝ) ≤ (d : ℝ) * (num : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self (d * num) den
    have hm_le : (m : ℝ) ≤ |valZ z u| * (num : ℝ) / (den : ℝ) := by
      rw [le_div_iff₀ hdenR, ← hd]; exact hm_mul
    have hm_z : m ≤ z := Nat.cast_le.mp (le_trans hm_le hmag)
    have hm_gt_nat : d * num < (m + 1) * den := by
      have h1 := Nat.div_add_mod (d * num) den
      have h2 := Nat.mod_lt (d * num) hden
      calc
        d * num = den * m + (d * num) % den := h1.symm
        _ < den * m + den := Nat.add_lt_add_left h2 _
        _ = (m + 1) * den := by ring
    have hm_gt : (d : ℝ) * (num : ℝ) < ((m : ℝ) + 1) * (den : ℝ) := by exact_mod_cast hm_gt_nat
    have hm_ge : |valZ z u| * (num : ℝ) / (den : ℝ) - 1 ≤ (m : ℝ) := by
      rw [sub_le_iff_le_add, div_le_iff₀ hdenR, ← hd]; linarith
    exact ⟨hm_z, hm_le, hm_ge⟩
  unfold onatMulDiv
  simp only [Nat.sub_eq, Nat.add_eq, Nat.mul_eq, nat_div_def]
  by_cases hzu : z ≤ u
  · have hb : Nat.ble z u = true := Nat.ble_eq.mpr hzu
    rw [hb, if_pos rfl]
    have hval_nn : 0 ≤ valZ z u := by unfold valZ; exact sub_nonneg.mpr (Nat.cast_le.mpr hzu)
    have hd : ((u - z : ℕ) : ℝ) = |valZ z u| := by
      rw [abs_of_nonneg hval_nn]; unfold valZ; exact Nat.cast_sub hzu
    obtain ⟨hm_z, hm_le_abs, hm_ge_abs⟩ := helper_div (u - z) hd
    let m := ((u - z) * num) / den
    have hm_le_orig : (m : ℝ) ≤ |valZ z u| * (num : ℝ) / (den : ℝ) := hm_le_abs
    have hm_le : (m : ℝ) ≤ valZ z u * (num : ℝ) / (den : ℝ) := by
      rwa [abs_of_nonneg hval_nn] at hm_le_abs
    have hm_ge : valZ z u * (num : ℝ) / (den : ℝ) - 1 ≤ (m : ℝ) := by
      rwa [abs_of_nonneg hval_nn] at hm_ge_abs
    change |valZ z (if neg then z - m else z + m) - signB neg * valZ z u * ↑num / ↑den| ≤ 1 ∧
      |valZ z (if neg then z - m else z + m)| ≤ |valZ z u| * ↑num / ↑den
    cases neg
    · simp only [Bool.false_eq_true, ↓reduceIte, signB, one_mul]
      have hv : valZ z (z + m) = (m : ℝ) := by unfold valZ; push_cast; ring
      rw [hv]
      refine ⟨abs_le.mpr ⟨by linarith only [hm_le, hm_ge], by linarith only [hm_le, hm_ge]⟩, ?_⟩
      rwa [abs_of_nonneg (Nat.cast_nonneg m)]
    · simp only [↓reduceIte, signB, neg_one_mul]
      have hv : valZ z (z - m) = -(m : ℝ) := by unfold valZ; rw [Nat.cast_sub hm_z]; ring
      rw [hv]
      have hex : -(valZ z u) * (num : ℝ) / (den : ℝ) = -(valZ z u * (num : ℝ) / (den : ℝ)) := by ring
      rw [hex]
      refine ⟨abs_le.mpr ⟨by linarith only [hm_le, hm_ge], by linarith only [hm_le, hm_ge]⟩, ?_⟩
      rwa [abs_neg, abs_of_nonneg (Nat.cast_nonneg m)]
  · have hb : Nat.ble z u = false := Bool.eq_false_iff.mpr fun ht => hzu (Nat.ble_eq.mp ht)
    rw [hb, if_neg Bool.false_ne_true]
    have hlt : u ≤ z := le_of_not_ge hzu
    have hval_np : valZ z u ≤ 0 := by unfold valZ; exact sub_nonpos.mpr (Nat.cast_le.mpr hlt)
    have hd : ((z - u : ℕ) : ℝ) = |valZ z u| := by
      rw [abs_of_nonpos hval_np]; unfold valZ; rw [Nat.cast_sub hlt]; ring
    obtain ⟨hm_z, hm_le_abs, hm_ge_abs⟩ := helper_div (z - u) hd
    let m := ((z - u) * num) / den
    have hm_le_orig : (m : ℝ) ≤ |valZ z u| * (num : ℝ) / (den : ℝ) := hm_le_abs
    have hm_le : (m : ℝ) ≤ -(valZ z u * (num : ℝ) / (den : ℝ)) := by
      rw [abs_of_nonpos hval_np] at hm_le_abs
      linarith [show -(valZ z u) * (num : ℝ) / (den : ℝ) = -(valZ z u * (num : ℝ) / (den : ℝ)) by ring]
    have hm_ge : -(valZ z u * (num : ℝ) / (den : ℝ)) - 1 ≤ (m : ℝ) := by
      rw [abs_of_nonpos hval_np] at hm_ge_abs
      linarith [show -(valZ z u) * (num : ℝ) / (den : ℝ) = -(valZ z u * (num : ℝ) / (den : ℝ)) by ring]
    change |valZ z (if neg then z + m else z - m) - signB neg * valZ z u * ↑num / ↑den| ≤ 1 ∧
      |valZ z (if neg then z + m else z - m)| ≤ |valZ z u| * ↑num / ↑den
    cases neg
    · simp only [Bool.false_eq_true, ↓reduceIte, signB, one_mul]
      have hv : valZ z (z - m) = -(m : ℝ) := by unfold valZ; rw [Nat.cast_sub hm_z]; ring
      rw [hv]
      refine ⟨abs_le.mpr ⟨by linarith only [hm_le, hm_ge], by linarith only [hm_le, hm_ge]⟩, ?_⟩
      rwa [abs_neg, abs_of_nonneg (Nat.cast_nonneg m)]
    · simp only [↓reduceIte, signB, neg_one_mul]
      have hv : valZ z (z + m) = (m : ℝ) := by unfold valZ; push_cast; ring
      rw [hv]
      have hex : -(valZ z u) * (num : ℝ) / (den : ℝ) = -(valZ z u * (num : ℝ) / (den : ℝ)) := by ring
      rw [hex]
      refine ⟨abs_le.mpr ⟨by linarith only [hm_le, hm_ge], by linarith only [hm_le, hm_ge]⟩, ?_⟩
      rwa [abs_of_nonneg (Nat.cast_nonneg m)]

lemma sumBTree_eq_sum {bt : BTree} {lo hi z : ℕ} {termFn : ℕ → ℕ → ℕ} {M : ℕ → ℝ}
    (hM : ∀ n ∈ Finset.Ico lo hi, 0 ≤ M n) (hshape : checkBShape bt lo hi = true)
    (hbd : ∀ n ∈ Finset.Ico lo hi, |valZ z (termFn (btreeGet bt lo hi n) n)| ≤ M n)
    (hZ : (∑ n ∈ Finset.Ico lo hi, M n) ≤ (z : ℝ) / 2) :
    valZ z (sumBTree z termFn bt lo hi) =
      ∑ n ∈ Finset.Ico lo hi, valZ z (termFn (btreeGet bt lo hi n) n) ∧
    |valZ z (sumBTree z termFn bt lo hi)| ≤ ∑ n ∈ Finset.Ico lo hi, M n := by
  induction bt generalizing lo hi with
  | L v =>
    simp only [checkBShape, Nat.add_eq, Nat.beq_eq] at hshape
    subst hshape
    have hIco : Finset.Ico lo (lo + 1) = {lo} := Nat.Ico_succ_singleton lo
    rw [hIco, Finset.sum_singleton, Finset.sum_singleton]
    exact ⟨rfl, hbd lo (by simp [hIco])⟩
  | N l r ihl ihr =>
    simp only [checkBShape, Bool.and_eq_true, Nat.ble_eq, Nat.add_eq, nat_div_def] at hshape
    obtain ⟨hlo_mid, hmid_hi, hsl, hsr⟩ := hshape
    let mid := (lo + hi) / 2
    have hlo_lt_mid : lo < mid := hlo_mid
    have hmid_lt_hi : mid < hi := hmid_hi
    have hget_l : ∀ n < mid, btreeGet (.N l r) lo hi n = btreeGet l lo mid n := by
      intro n hnm
      conv_lhs => unfold btreeGet; simp only [Nat.add_eq, nat_div_def]
      have hnb : Nat.ble ((lo + hi) / 2) n = false :=
        Bool.eq_false_iff.mpr fun ht => not_le_of_gt hnm (Nat.ble_eq.mp ht)
      rw [hnb, if_neg Bool.false_ne_true]
    have hget_r : ∀ n, mid ≤ n → btreeGet (.N l r) lo hi n = btreeGet r mid hi n := by
      intro n hmn
      conv_lhs => unfold btreeGet; simp only [Nat.add_eq, nat_div_def]
      have hnb : Nat.ble ((lo + hi) / 2) n = true := Nat.ble_eq.mpr hmn
      rw [hnb, if_pos rfl]
    have hM_l : ∀ n ∈ Finset.Ico lo mid, 0 ≤ M n := fun n hn =>
      hM n (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hn).1, lt_trans (Finset.mem_Ico.mp hn).2 hmid_lt_hi⟩)
    have hM_r : ∀ n ∈ Finset.Ico mid hi, 0 ≤ M n := fun n hn =>
      hM n (Finset.mem_Ico.mpr ⟨le_trans hlo_lt_mid.le (Finset.mem_Ico.mp hn).1, (Finset.mem_Ico.mp hn).2⟩)
    have hbd_l : ∀ n ∈ Finset.Ico lo mid, |valZ z (termFn (btreeGet l lo mid n) n)| ≤ M n := by
      intro n hn
      rw [← hget_l n (Finset.mem_Ico.mp hn).2]
      exact hbd n (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hn).1, lt_trans (Finset.mem_Ico.mp hn).2 hmid_lt_hi⟩)
    have hbd_r : ∀ n ∈ Finset.Ico mid hi, |valZ z (termFn (btreeGet r mid hi n) n)| ≤ M n := by
      intro n hn
      rw [← hget_r n (Finset.mem_Ico.mp hn).1]
      exact hbd n (Finset.mem_Ico.mpr ⟨le_trans hlo_lt_mid.le (Finset.mem_Ico.mp hn).1, (Finset.mem_Ico.mp hn).2⟩)
    have hM_split : (∑ n ∈ Finset.Ico lo mid, M n) + (∑ n ∈ Finset.Ico mid hi, M n) = ∑ n ∈ Finset.Ico lo hi, M n :=
      Finset.sum_Ico_consecutive M hlo_lt_mid.le hmid_lt_hi.le
    have hMl_nn : 0 ≤ ∑ n ∈ Finset.Ico lo mid, M n := Finset.sum_nonneg hM_l
    have hMr_nn : 0 ≤ ∑ n ∈ Finset.Ico mid hi, M n := Finset.sum_nonneg hM_r
    have hZl : (∑ n ∈ Finset.Ico lo mid, M n) ≤ (z : ℝ) / 2 := by linarith
    have hZr : (∑ n ∈ Finset.Ico mid hi, M n) ≤ (z : ℝ) / 2 := by linarith
    obtain ⟨heql, hbdl_sum⟩ := ihl hM_l hsl hbd_l hZl
    obtain ⟨heqr, hbdr_sum⟩ := ihr hM_r hsr hbd_r hZr
    have hal : -(z : ℝ) / 2 ≤ valZ z (sumBTree z termFn l lo mid) := by
      have := neg_abs_le (valZ z (sumBTree z termFn l lo mid)); linarith
    have har : -(z : ℝ) / 2 ≤ valZ z (sumBTree z termFn r mid hi) := by
      have := neg_abs_le (valZ z (sumBTree z termFn r mid hi)); linarith
    have hsum_unfold : sumBTree z termFn (.N l r) lo hi =
        onatAdd z (sumBTree z termFn l lo mid) (sumBTree z termFn r mid hi) := rfl
    rw [hsum_unfold, valZ_onatAdd hal har]
    refine ⟨?_, ?_⟩
    · rw [heql, heqr]
      rw [← Finset.sum_Ico_consecutive (fun n => valZ z (termFn (btreeGet (.N l r) lo hi n) n)) hlo_lt_mid.le hmid_lt_hi.le]
      congr 1
      · refine Finset.sum_congr rfl fun n hn => ?_
        rw [hget_l n (Finset.mem_Ico.mp hn).2]
      · refine Finset.sum_congr rfl fun n hn => ?_
        rw [hget_r n (Finset.mem_Ico.mp hn).1]
    · calc
        |valZ z (sumBTree z termFn l lo mid) + valZ z (sumBTree z termFn r mid hi)|
          ≤ |valZ z (sumBTree z termFn l lo mid)| + |valZ z (sumBTree z termFn r mid hi)| := abs_add_le _ _
        _ ≤ (∑ n ∈ Finset.Ico lo mid, M n) + (∑ n ∈ Finset.Ico mid hi, M n) := add_le_add hbdl_sum hbdr_sum
        _ = ∑ n ∈ Finset.Ico lo hi, M n := hM_split

end
end GaussSmallBridge

namespace GaussSmallBridge
noncomputable section

/-! ### Part 4B-2: `checkBTree` Drift Bound and `term0R..termT2I` Complex Coefficient Soundness -/

def S_nat : ℕ := 1208925819614629174706176
def Z_nat : ℕ := 1329227995784915872903807060280344576
def PAD_nat : ℕ := 18014398509481984
def PI0_DEN_nat : ℕ := 100000000000
def W6_NUM_nat : ℕ := 1884955592154
def W6_HI_nat : ℕ := 22787714841819531240894044
def ERR0_nat : ℕ := 1549904896941832275265
def ERRD_nat : ℕ := 201487636602438195785
def ERRT_nat : ℕ := 60446290980731458736
def ERRT2_nat : ℕ := 120892581961462917471
def E_SUM : ℝ := 5100000000000000

lemma S_nat_eq : S_nat = 1208925819614629174706176 := rfl
lemma Z_nat_eq : Z_nat = 1329227995784915872903807060280344576 := rfl
lemma PAD_nat_eq : PAD_nat = 18014398509481984 := rfl
lemma PI0_DEN_nat_eq : PI0_DEN_nat = 100000000000 := rfl
lemma W6_NUM_nat_eq : W6_NUM_nat = 1884955592154 := rfl
lemma W6_HI_nat_eq : W6_HI_nat = 22787714841819531240894044 := rfl
lemma ERR0_nat_eq : ERR0_nat = 1549904896941832275265 := rfl
lemma ERRD_nat_eq : ERRD_nat = 201487636602438195785 := rfl
lemma ERRT_nat_eq : ERRT_nat = 60446290980731458736 := rfl
lemma ERRT2_nat_eq : ERRT2_nat = 120892581961462917471 := rfl

lemma S_nat_pos_nat : 0 < S_nat := by unfold S_nat; norm_num
lemma PI0_DEN_nat_pos : 0 < PI0_DEN_nat := by unfold PI0_DEN_nat; norm_num
lemma S_nat_pos : (0 : ℝ) < (S_nat : ℝ) := Nat.cast_pos.mpr S_nat_pos_nat
lemma Z_nat_pos : (0 : ℝ) < (Z_nat : ℝ) := by unfold Z_nat; norm_num
lemma E_SUM_pos : 0 < E_SUM := by unfold E_SUM; norm_num
lemma S_le_B_mag : (S_nat : ℝ) ≤ (S_nat : ℝ) * 3 ^ 22 + 20000 * 3 ^ 22 := by unfold S_nat; norm_num
lemma S_mul_19_le_Z : (S_nat : ℝ) * 19 ≤ (Z_nat : ℝ) := by unfold S_nat Z_nat; norm_num
lemma B_mag_le_Z_div_30 : (S_nat : ℝ) * 3 ^ 22 + 20000 * 3 ^ 22 ≤ (Z_nat : ℝ) / 30 := by
  unfold S_nat Z_nat; norm_num
lemma sumM_bound_le_Z_div_2 : 8 * ((S_nat : ℝ) * 3 ^ 22 + 20000 * 3 ^ 22) ≤ (Z_nat : ℝ) / 2 := by
  unfold S_nat Z_nat; norm_num
lemma sum_err_96_le_E_SUM : (96 : ℝ) + 8 * (20000 * 3 ^ 22) ≤ E_SUM := by unfold E_SUM; norm_num
lemma S_polyJ_le_Z_div_4 : (S_nat : ℝ) * (8 * 3 ^ 22) + E_SUM ≤ (Z_nat : ℝ) / 4 := by
  unfold S_nat E_SUM Z_nat; norm_num
lemma E_SUM_le_PAD : E_SUM ≤ (PAD_nat : ℝ) := by unfold E_SUM PAD_nat; norm_num
lemma three_E_SUM_add_two_le_PAD : 3 * E_SUM + 2 ≤ (PAD_nat : ℝ) := by unfold E_SUM PAD_nat; norm_num
lemma S_err0_le : (S_nat : ℝ) * (1 / 780) ≤ (ERR0_nat : ℝ) := by unfold S_nat ERR0_nat; norm_num
lemma S_errD_le : (S_nat : ℝ) * (1 / 6000) ≤ (ERRD_nat : ℝ) := by unfold S_nat ERRD_nat; norm_num
lemma S_errT_le : (S_nat : ℝ) * (1 / 20000) ≤ (ERRT_nat : ℝ) := by unfold S_nat ERRT_nat; norm_num
lemma S_errT2_le : (S_nat : ℝ) * (1 / 10000) ≤ (ERRT2_nat : ℝ) := by unfold S_nat ERRT2_nat; norm_num
lemma w6_pi0_le : 6 * pi0R ≤ (W6_HI_nat : ℝ) / (S_nat : ℝ) := by unfold pi0R W6_HI_nat S_nat; norm_num
lemma w6_num_eq_pi0 : (W6_NUM_nat : ℝ) = 6 * pi0R * (PI0_DEN_nat : ℝ) := by
  unfold W6_NUM_nat pi0R PI0_DEN_nat; norm_num

attribute [irreducible] S_nat Z_nat PAD_nat PI0_DEN_nat W6_NUM_nat W6_HI_nat
  ERR0_nat ERRD_nat ERRT_nat ERRT2_nat E_SUM pi0R

def uSeq : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | n + 2 => (19 * uSeq (n + 1) + 9 * uSeq n + 2 * ((n : ℝ) + 2)) / ((n : ℝ) + 2)

lemma uSeq_rec (n : ℕ) :
    ((n : ℝ) + 2) * uSeq (n + 2) = 19 * uSeq (n + 1) + 9 * uSeq n + 2 * ((n : ℝ) + 2) := by
  have hne : ((n : ℝ) + 2) ≠ 0 := by positivity
  dsimp [uSeq]
  exact mul_div_cancel₀ _ hne

lemma uSeq_nonneg_pair (n : ℕ) : 0 ≤ uSeq n ∧ 0 ≤ uSeq (n + 1) := by
  induction n with
  | zero => dsimp [uSeq]; norm_num
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    dsimp [uSeq]
    exact div_nonneg (by linarith [ih.1, ih.2, Nat.cast_nonneg (α := ℝ) k]) (by positivity)

lemma uSeq_nonneg (n : ℕ) : 0 ≤ uSeq n := (uSeq_nonneg_pair n).1

def uPoly : ℕ → ℝ → ℝ
  | 0, _ => 0
  | m + 1, x => uPoly m x + uSeq (m + 1) * x ^ (m + 1)

def uPolyDeriv : ℕ → ℝ → ℝ
  | 0, _ => 0
  | m + 1, x => uPolyDeriv m x + ((m : ℝ) + 1) * uSeq (m + 1) * x ^ m

def inhomSum : ℕ → ℝ → ℝ
  | 0, _ => 1
  | m + 1, x => inhomSum m x + 2 * ((m : ℝ) + 2) * x ^ (m + 1)

lemma hasDerivAt_uPoly (m : ℕ) (x : ℝ) : HasDerivAt (uPoly m) (uPolyDeriv m x) x := by
  induction m with
  | zero => simpa [uPoly, uPolyDeriv] using hasDerivAt_const x (0 : ℝ)
  | succ m ih =>
    dsimp [uPoly, uPolyDeriv]
    have hpow : HasDerivAt (fun u : ℝ => uSeq (m + 1) * u ^ (m + 1))
        (((m : ℝ) + 1) * uSeq (m + 1) * x ^ m) x := by
      simpa [Nat.cast_add, Nat.cast_one, mul_comm, mul_left_comm, mul_assoc] using
        (hasDerivAt_pow (m + 1) x).const_mul (uSeq (m + 1))
    exact ih.add hpow

lemma uPoly_ode_id (m : ℕ) (x : ℝ) :
    uPolyDeriv m x - (19 + 9 * x) * uPoly m x =
      -(((m : ℝ) + 1) * uSeq (m + 1) * x ^ m + 9 * uSeq m * x ^ (m + 1)) + inhomSum m x := by
  induction m with
  | zero => simp [uPoly, uPolyDeriv, inhomSum, uSeq]
  | succ m ih =>
    have hrec := uSeq_rec m
    change (uPolyDeriv m x + ((m : ℝ) + 1) * uSeq (m + 1) * x ^ m) -
        (19 + 9 * x) * (uPoly m x + uSeq (m + 1) * x ^ (m + 1)) =
      -((((m + 1 : ℕ) : ℝ) + 1) * uSeq (m + 2) * x ^ (m + 1) + 9 * uSeq (m + 1) * x ^ (m + 2)) +
        (inhomSum m x + 2 * ((m : ℝ) + 2) * x ^ (m + 1))
    push_cast
    linear_combination ih + x ^ (m + 1) * hrec

lemma inhomSum_le (m : ℕ) (hm : m ≤ 98) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    inhomSum m x ≤ 1 + 200 * (m : ℝ) := by
  induction m with
  | zero => simp [inhomSum]
  | succ k ih =>
    have hk : k ≤ 98 := Nat.le_of_succ_le hm
    have h1 := ih hk
    dsimp [inhomSum]
    have hxpow : x ^ (k + 1) ≤ 1 := pow_le_one₀ hx0 hx1
    have h2 : 2 * ((k : ℝ) + 2) ≤ 200 := by
      have hkR : (k : ℝ) ≤ 98 := by exact_mod_cast hk
      linarith
    have hmul : 2 * ((k : ℝ) + 2) * x ^ (k + 1) ≤ 200 := by
      calc
        2 * ((k : ℝ) + 2) * x ^ (k + 1) ≤ 2 * ((k : ℝ) + 2) * 1 :=
          mul_le_mul_of_nonneg_left hxpow (by positivity)
        _ ≤ 200 := by linarith
    push_cast
    linarith

lemma uPoly_95_one_le :
    uPoly 95 1 ≤ 20000 * 3 ^ 22 ∧
    (∑ n ∈ Finset.Ico 0 96, uSeq n) ≤ 20000 * 3 ^ 22 ∧
    (∀ n < 96, uSeq n ≤ 20000 * 3 ^ 22) := by
  let G : ℝ → ℝ := fun u => Real.exp (-(19 * u + 9 / 2 * u ^ 2)) * uPoly 95 u
  let G' : ℝ → ℝ := fun u =>
    Real.exp (-(19 * u + 9 / 2 * u ^ 2)) * (uPolyDeriv 95 u - (19 + 9 * u) * uPoly 95 u)
  have hderiv : ∀ u : ℝ, HasDerivAt G (G' u) u := by
    intro u
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-(19 * t + 9 / 2 * t ^ 2)))
        (-(19 + 9 * u) * Real.exp (-(19 * u + 9 / 2 * u ^ 2))) u := by
      have hp : HasDerivAt (fun t : ℝ => -(19 * t + 9 / 2 * t ^ 2)) (-(19 + 9 * u)) u :=
        (((hasDerivAt_id u).const_mul (19 : ℝ)).add ((hasDerivAt_pow 2 u).const_mul (9 / 2 : ℝ))).neg.congr_deriv (by ring)
      exact hp.exp.congr_deriv (by ring)
    exact (hexp.mul (hasDerivAt_uPoly 95 u)).congr_deriv (by dsimp [G']; ring)
  have hcont : Continuous G' := by
    have hm : Continuous (uPoly 95) :=
      continuous_iff_continuousAt.mpr fun u => (hasDerivAt_uPoly 95 u).continuousAt
    have hmd : Continuous (uPolyDeriv 95) := by
      clear G G' hderiv hm
      induction (95 : ℕ) with
      | zero => exact continuous_const
      | succ k ih => dsimp [uPolyDeriv]; exact ih.add (continuous_const.mul (continuous_pow k))
    dsimp [G']
    exact (Real.continuous_exp.comp (by fun_prop)).mul
      (hmd.sub ((by fun_prop : Continuous fun u : ℝ => 19 + 9 * u).mul hm))
  have hG0 : G 0 = 0 := by
    dsimp [G]
    have hu0 : uPoly 95 0 = 0 := by
      clear G G' hderiv hcont
      induction (95 : ℕ) with
      | zero => rfl
      | succ k ih => simp [uPoly, ih]
    simp [hu0]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u)
    (hcont.intervalIntegrable 0 1)
  rw [hG0, sub_zero] at hftc
  have hG'_le : ∀ u ∈ Ioc (0 : ℝ) 1, G' u ≤ 20000 := by
    intro u hu
    dsimp [G']
    rw [uPoly_ode_id]
    have hinh := inhomSum_le 95 (by norm_num) hu.1.le hu.2
    have hnn : 0 ≤ ((95 : ℝ) + 1) * uSeq 96 * u ^ 95 + 9 * uSeq 95 * u ^ 96 :=
      add_nonneg (mul_nonneg (mul_nonneg (by positivity) (uSeq_nonneg 96)) (pow_nonneg hu.1.le _))
        (mul_nonneg (mul_nonneg (by norm_num) (uSeq_nonneg 95)) (pow_nonneg hu.1.le _))
    have h1 : -(((95 : ℝ) + 1) * uSeq 96 * u ^ 95 + 9 * uSeq 95 * u ^ 96) + inhomSum 95 u ≤ 20000 := by
      norm_num at hinh; linarith
    have hexp1 : Real.exp (-(19 * u + 9 / 2 * u ^ 2)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hu.1, sq_nonneg u])
    rcases le_total 0 (-(((95 : ℝ) + 1) * uSeq 96 * u ^ 95 + 9 * uSeq 95 * u ^ 96) + inhomSum 95 u) with hsg | hsg
    · exact le_trans (mul_le_mul hexp1 h1 hsg zero_le_one) (by norm_num)
    · exact le_trans (mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) hsg) (by norm_num)
  have hint_le : ∫ u in (0)..1, G' u ≤ 20000 := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    have h20000 : ∫ _ : ℝ in Ioc (0 : ℝ) 1, (20000 : ℝ) = 20000 := by simp
    rw [← h20000]
    exact integral_mono_ae (hcont.integrableOn_Ioc) (continuous_const.integrableOn_Ioc)
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hG'_le))
  have hG1 : G 1 ≤ 20000 := by linarith
  dsimp [G] at hG1
  have hexp_pos : 0 < Real.exp (19 * (1 : ℝ) + 9 / 2 * (1 : ℝ) ^ 2) := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_left hG1 hexp_pos.le
  rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at hmul
  have hexp47 : Real.exp (19 * (1 : ℝ) + 9 / 2 * (1 : ℝ) ^ 2) ≤ 3 ^ 22 := by
    have he_hi : Real.exp 1 < 2719 / 1000 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hsq : (Real.exp (19 * (1 : ℝ) + 9 / 2 * (1 : ℝ) ^ 2)) ^ 2 ≤ ((3 : ℝ) ^ 22) ^ 2 := by
      have : (Real.exp (19 * (1 : ℝ) + 9 / 2 * (1 : ℝ) ^ 2)) ^ 2 = (Real.exp 1) ^ 47 := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; congr 1; norm_num
      rw [this]
      exact le_trans (pow_le_pow_left₀ (Real.exp_nonneg _) he_hi.le 47) (by norm_num)
    by_contra hgt; push Not at hgt
    have := pow_lt_pow_left₀ hgt (by positivity) (by norm_num : 2 ≠ 0)
    linarith
  have hu95 : uPoly 95 1 ≤ 20000 * 3 ^ 22 :=
    le_trans hmul (by linarith [mul_le_mul_of_nonneg_right hexp47 (by norm_num : (0 : ℝ) ≤ 20000)])
  have hsum_eq : ∀ m : ℕ, uPoly m 1 = ∑ n ∈ Finset.Ico 0 (m + 1), uSeq n := by
    intro m
    induction m with
    | zero => simp [uPoly, uSeq]
    | succ k ih =>
      rw [Nat.Ico_zero_eq_range, Finset.sum_range_succ, ← Nat.Ico_zero_eq_range, ← ih]
      simp [uPoly]
  have hsum_le : (∑ n ∈ Finset.Ico 0 96, uSeq n) ≤ 20000 * 3 ^ 22 := by
    rwa [← hsum_eq 95]
  refine ⟨hu95, hsum_le, ?_⟩
  intro n hn
  have hmem : n ∈ Finset.Ico 0 96 := Finset.mem_Ico.mpr ⟨Nat.zero_le n, hn⟩
  exact le_trans (Finset.single_le_sum (fun k _ => uSeq_nonneg k) hmem) hsum_le

attribute [irreducible] uPoly uPolyDeriv inhomSum

lemma aMaj_le_3_pow_22 (n : ℕ) (hn : n < 96) : aMaj n ≤ 3 ^ 22 := by
  obtain ⟨_, _, hm1⟩ := aMaj_95_96_bounds
  have hsum_eq : ∀ m : ℕ, majPoly m 1 = ∑ k ∈ Finset.range (m + 1), aMaj k := by
    intro m
    induction m with
    | zero => simp [majPoly, aMaj, bEx]
    | succ k ih => rw [Finset.sum_range_succ, ← ih]; simp [majPoly]
  rw [hsum_eq 95] at hm1
  exact le_trans (Finset.single_le_sum (fun k _ => aMaj_nonneg k) (Finset.mem_range.mpr hn)) hm1

lemma checkBLoop_get {z denBase numW : ℕ} {dNeg : Bool} {bt : BTree} {k start : ℕ}
    (h : checkBLoop z denBase numW dNeg bt k start = true) :
    ∀ j < k, checkBStep z denBase numW dNeg bt (start + j) = true := by
  induction k generalizing start with
  | zero => intro j hj; omega
  | succ k ih =>
    simp only [checkBLoop, Bool.and_eq_true, Nat.add_eq] at h
    intro j hj
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have hj' : j < k := Nat.lt_of_succ_lt_succ hj
      have := ih h.2 j hj'
      rwa [show start + 1 + j = start + (j + 1) by omega] at this

lemma checkBTree_sound {denBase numW : ℕ} {dNeg : Bool} {bt : BTree}
    (hden : 0 < denBase)
    (hω : |signB dNeg * (numW : ℝ) / (denBase : ℝ)| ≤ 19)
    (hchk : checkBTree S_nat Z_nat denBase numW dNeg bt = true) :
    let ω := signB dNeg * (numW : ℝ) / (denBase : ℝ)
    checkBShape bt 0 96 = true ∧
    ∀ n < 96,
      |valZ Z_nat (btreeGet bt 0 96 n) - (S_nat : ℝ) * bEx ω n| ≤ uSeq n ∧
      |valZ Z_nat (btreeGet bt 0 96 n)| ≤ (S_nat : ℝ) * 3 ^ 22 + 20000 * 3 ^ 22 := by
  intro ω
  simp only [checkBTree, Bool.and_eq_true, Nat.beq_eq, Nat.add_eq] at hchk
  obtain ⟨hshape, hb0_eq, hb1_eq, hloop⟩ := hchk
  refine ⟨hshape, ?_⟩
  have hstep_all := checkBLoop_get hloop
  obtain ⟨_, _, hu_bound⟩ := uPoly_95_one_le
  have hnum_over_den : (numW : ℝ) / (denBase : ℝ) ≤ 19 := by
    have : |signB dNeg * (numW : ℝ) / (denBase : ℝ)| = (numW : ℝ) / (denBase : ℝ) := by
      rw [abs_div, abs_mul, abs_signB, one_mul,
        abs_of_nonneg (Nat.cast_nonneg numW), abs_of_pos (Nat.cast_pos.mpr hden)]
    linarith
  have hpair : ∀ m ≤ 94,
      (|valZ Z_nat (btreeGet bt 0 96 m) - (S_nat : ℝ) * bEx ω m| ≤ uSeq m ∧
        |valZ Z_nat (btreeGet bt 0 96 m)| ≤ (S_nat : ℝ) * 3 ^ 22 + 20000 * 3 ^ 22) ∧
      (|valZ Z_nat (btreeGet bt 0 96 (m + 1)) - (S_nat : ℝ) * bEx ω (m + 1)| ≤ uSeq (m + 1) ∧
        |valZ Z_nat (btreeGet bt 0 96 (m + 1))| ≤ (S_nat : ℝ) * 3 ^ 22 + 20000 * 3 ^ 22) := by
    intro m hm
    induction m with
    | zero =>
      have hv0 : valZ Z_nat (btreeGet bt 0 96 0) = (S_nat : ℝ) := by
        rw [hb0_eq]; unfold valZ; push_cast; ring
      have he0 : |valZ Z_nat (btreeGet bt 0 96 0) - (S_nat : ℝ) * bEx ω 0| ≤ uSeq 0 := by
        rw [hv0]; simp [bEx, uSeq]
      have hmag0 : |valZ Z_nat (btreeGet bt 0 96 0)| ≤ (S_nat : ℝ) * 3 ^ 22 + 20000 * 3 ^ 22 := by
        rw [hv0, abs_of_pos S_nat_pos]; exact S_le_B_mag
      have hv0' : valZ Z_nat (Z_nat + S_nat) = (S_nat : ℝ) := by unfold valZ; push_cast; ring
      have h1_guard : |valZ Z_nat (Z_nat + S_nat)| * (numW : ℝ) / (denBase : ℝ) ≤ (Z_nat : ℝ) := by
        rw [hv0', abs_of_pos S_nat_pos]
        have hmul : (S_nat : ℝ) * ((numW : ℝ) / (denBase : ℝ)) ≤ (S_nat : ℝ) * 19 :=
          mul_le_mul_of_nonneg_left hnum_over_den S_nat_pos.le
        linarith [S_mul_19_le_Z, mul_div_assoc (S_nat : ℝ) (numW : ℝ) (denBase : ℝ)]
      obtain ⟨herr1, _⟩ := valZ_onatMulDiv_approx dNeg hden h1_guard
      have he1 : |valZ Z_nat (btreeGet bt 0 96 1) - (S_nat : ℝ) * bEx ω 1| ≤ uSeq 1 := by
        rw [hb1_eq]
        have hex : signB dNeg * valZ Z_nat (Z_nat + S_nat) * (numW : ℝ) / (denBase : ℝ) =
            (S_nat : ℝ) * bEx ω 1 := by
          rw [hv0']; dsimp [bEx, ω]; ring
        rw [← hex]; simpa [uSeq] using herr1
      have hmag1 : |valZ Z_nat (btreeGet bt 0 96 1)| ≤ (S_nat : ℝ) * 3 ^ 22 + 20000 * 3 ^ 22 := by
        have hb_ex := (aMaj_nonneg_and_bEx_le hω 1).1.2
        have ha1 := aMaj_le_3_pow_22 1 (by norm_num)
        have hu1 := hu_bound 1 (by norm_num)
        have htri := abs_le_abs_add_err (valZ Z_nat (btreeGet bt 0 96 1)) ((S_nat : ℝ) * bEx ω 1)
        rw [abs_mul, abs_of_pos S_nat_pos] at htri
        have hS : (S_nat : ℝ) * |bEx ω 1| ≤ (S_nat : ℝ) * 3 ^ 22 :=
          mul_le_mul_of_nonneg_left (le_trans hb_ex ha1) S_nat_pos.le
        linarith
      exact ⟨⟨he0, hmag0⟩, ⟨he1, hmag1⟩⟩
    | succ k ih =>
      have hk : k ≤ 94 := Nat.le_of_succ_le hm
      obtain ⟨⟨he_k, hmag_k⟩, ⟨he_k1, hmag_k1⟩⟩ := ih hk
      refine ⟨⟨he_k1, hmag_k1⟩, ?_⟩
      have hst := hstep_all k (by omega)
      rw [show 1 + k = k + 1 by omega] at hst
      simp only [checkBStep, Nat.beq_eq, Nat.add_eq, Nat.sub_eq, Nat.mul_eq] at hst
      have hk_sub : k + 1 - 1 = k := Nat.add_sub_cancel k 1
      rw [hk_sub] at hst
      let bPrev := btreeGet bt 0 96 k
      let bCurr := btreeGet bt 0 96 (k + 1)
      let n1 := k + 2
      have hn1_pos : 0 < n1 := by dsimp [n1]; omega
      have hden1_pos : 0 < denBase * n1 := Nat.mul_pos hden hn1_pos
      have hn1_ge2 : (2 : ℝ) ≤ (n1 : ℝ) := by dsimp [n1]; norm_cast; omega
      have hg1 : |valZ Z_nat bCurr| * (numW : ℝ) / ((denBase * n1 : ℕ) : ℝ) ≤ (Z_nat : ℝ) / 2 := by
        rw [Nat.cast_mul]
        have h1 : (numW : ℝ) / ((denBase : ℝ) * (n1 : ℝ)) ≤ 19 / 2 := by
          rw [← div_div]
          have hd2 : ((numW : ℝ) / (denBase : ℝ)) / (n1 : ℝ) ≤ ((numW : ℝ) / (denBase : ℝ)) / 2 :=
            div_le_div_of_nonneg_left (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by norm_num) hn1_ge2
          linarith
        calc
          |valZ Z_nat bCurr| * (numW : ℝ) / ((denBase : ℝ) * (n1 : ℝ))
            = |valZ Z_nat bCurr| * ((numW : ℝ) / ((denBase : ℝ) * (n1 : ℝ))) := mul_div_assoc _ _ _
          _ ≤ ((Z_nat : ℝ) / 30) * (19 / 2) :=
              mul_le_mul (le_trans hmag_k1 B_mag_le_Z_div_30) h1
                (div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
                (div_nonneg Z_nat_pos.le (by norm_num))
          _ ≤ (Z_nat : ℝ) / 2 := by linarith [Z_nat_pos]
      have hg2 : |valZ Z_nat bPrev| * (9 : ℝ) / (n1 : ℝ) ≤ (Z_nat : ℝ) / 2 := by
        have h9 : (9 : ℝ) / (n1 : ℝ) ≤ 9 / 2 :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn1_ge2
        calc
          |valZ Z_nat bPrev| * (9 : ℝ) / (n1 : ℝ) = |valZ Z_nat bPrev| * ((9 : ℝ) / (n1 : ℝ)) := mul_div_assoc _ _ _
          _ ≤ ((Z_nat : ℝ) / 30) * (9 / 2) :=
              mul_le_mul (le_trans hmag_k B_mag_le_Z_div_30) h9
                (div_nonneg (by norm_num) (Nat.cast_nonneg _))
                (div_nonneg Z_nat_pos.le (by norm_num))
          _ ≤ (Z_nat : ℝ) / 2 := by linarith [Z_nat_pos]
      obtain ⟨herr_t1, hmag_t1⟩ := valZ_onatMulDiv_approx dNeg hden1_pos
        (le_trans hg1 (by linarith [Z_nat_pos]))
      obtain ⟨herr_t2, hmag_t2⟩ := valZ_onatMulDiv_approx false hn1_pos
        (le_trans hg2 (by linarith [Z_nat_pos]))
      let t1 := onatMulDiv Z_nat bCurr dNeg numW (denBase * n1)
      let t2 := onatMulDiv Z_nat bPrev false 9 n1
      have ha_t1 : -(Z_nat : ℝ) / 2 ≤ valZ Z_nat t1 := by
        have := neg_abs_le (valZ Z_nat t1); linarith [le_trans hmag_t1 hg1]
      have ha_t2 : -(Z_nat : ℝ) / 2 ≤ valZ Z_nat t2 := by
        have := neg_abs_le (valZ Z_nat t2); linarith [le_trans hmag_t2 hg2]
      have hnext_val : valZ Z_nat (btreeGet bt 0 96 (k + 1 + 1)) = valZ Z_nat t1 + valZ Z_nat t2 := by
        rw [hst, valZ_onatAdd ha_t1 ha_t2]
      have hex_rec : (S_nat : ℝ) * bEx ω (k + 2) =
          (ω * ((S_nat : ℝ) * bEx ω (k + 1)) + 9 * ((S_nat : ℝ) * bEx ω k)) / ((k : ℝ) + 2) := by
        dsimp [bEx]; ring
      have ht1_id : signB dNeg * valZ Z_nat bCurr * (numW : ℝ) / ((denBase * n1 : ℕ) : ℝ) =
          ω * valZ Z_nat bCurr / ((k : ℝ) + 2) := by
        have hdenR_ne : (denBase : ℝ) ≠ 0 := (Nat.cast_pos.mpr hden).ne'
        have hk2_ne : ((k : ℝ) + 2) ≠ 0 := by positivity
        dsimp [ω, n1]; push_cast; field_simp [hdenR_ne, hk2_ne]
      have ht2_id : signB false * valZ Z_nat bPrev * ((9 : ℕ) : ℝ) / (n1 : ℝ) =
          9 * valZ Z_nat bPrev / ((k : ℝ) + 2) := by
        dsimp [signB, n1]; push_cast; ring
      rw [ht1_id] at herr_t1
      rw [ht2_id] at herr_t2
      have he_k2 : |valZ Z_nat (btreeGet bt 0 96 (k + 2)) - (S_nat : ℝ) * bEx ω (k + 2)| ≤ uSeq (k + 2) := by
        change |valZ Z_nat (btreeGet bt 0 96 (k + 1 + 1)) - (S_nat : ℝ) * bEx ω (k + 2)| ≤ uSeq (k + 2)
        rw [hnext_val, hex_rec]
        have hne : ((k : ℝ) + 2) ≠ 0 := by positivity
        have hsplit : (valZ Z_nat t1 + valZ Z_nat t2) -
            (ω * ((S_nat : ℝ) * bEx ω (k + 1)) + 9 * ((S_nat : ℝ) * bEx ω k)) / ((k : ℝ) + 2) =
          (valZ Z_nat t1 - ω * valZ Z_nat bCurr / ((k : ℝ) + 2)) +
          (valZ Z_nat t2 - 9 * valZ Z_nat bPrev / ((k : ℝ) + 2)) +
          (ω * (valZ Z_nat bCurr - (S_nat : ℝ) * bEx ω (k + 1)) +
            9 * (valZ Z_nat bPrev - (S_nat : ℝ) * bEx ω k)) / ((k : ℝ) + 2) := by
          field_simp [hne]; ring
        rw [hsplit]
        have htri1 := abs_add_le
          ((valZ Z_nat t1 - ω * valZ Z_nat bCurr / ((k : ℝ) + 2)) +
            (valZ Z_nat t2 - 9 * valZ Z_nat bPrev / ((k : ℝ) + 2)))
          ((ω * (valZ Z_nat bCurr - (S_nat : ℝ) * bEx ω (k + 1)) +
            9 * (valZ Z_nat bPrev - (S_nat : ℝ) * bEx ω k)) / ((k : ℝ) + 2))
        have htri2 := abs_add_le
          (valZ Z_nat t1 - ω * valZ Z_nat bCurr / ((k : ℝ) + 2))
          (valZ Z_nat t2 - 9 * valZ Z_nat bPrev / ((k : ℝ) + 2))
        have hk2_pos : (0 : ℝ) < (k : ℝ) + 2 := by positivity
        have hprop : |(ω * (valZ Z_nat bCurr - (S_nat : ℝ) * bEx ω (k + 1)) +
            9 * (valZ Z_nat bPrev - (S_nat : ℝ) * bEx ω k)) / ((k : ℝ) + 2)| ≤
            (19 * uSeq (k + 1) + 9 * uSeq k) / ((k : ℝ) + 2) := by
          rw [abs_div, abs_of_pos hk2_pos]
          refine div_le_div_of_nonneg_right ?_ hk2_pos.le
          have hm1 : |ω * (valZ Z_nat bCurr - (S_nat : ℝ) * bEx ω (k + 1))| ≤ 19 * uSeq (k + 1) := by
            rw [abs_mul]; exact mul_le_mul hω he_k1 (abs_nonneg _) (by norm_num)
          have hm2 : |9 * (valZ Z_nat bPrev - (S_nat : ℝ) * bEx ω k)| ≤ 9 * uSeq k := by
            rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 9)]
            exact mul_le_mul_of_nonneg_left he_k (by norm_num)
          exact le_trans (abs_add_le _ _) (add_le_add hm1 hm2)
        have hu_eq : 2 + (19 * uSeq (k + 1) + 9 * uSeq k) / ((k : ℝ) + 2) = uSeq (k + 2) := by
          dsimp [uSeq]; field_simp [hne]; ring
        linarith
      have hmag_k2 : |valZ Z_nat (btreeGet bt 0 96 (k + 2))| ≤ (S_nat : ℝ) * 3 ^ 22 + 20000 * 3 ^ 22 := by
        have hb_ex := (aMaj_nonneg_and_bEx_le hω (k + 2)).1.2
        have ha2 := aMaj_le_3_pow_22 (k + 2) (by omega)
        have hu2 := hu_bound (k + 2) (by omega)
        have htri := abs_le_abs_add_err (valZ Z_nat (btreeGet bt 0 96 (k + 2))) ((S_nat : ℝ) * bEx ω (k + 2))
        rw [abs_mul, abs_of_pos S_nat_pos] at htri
        have hS : (S_nat : ℝ) * |bEx ω (k + 2)| ≤ (S_nat : ℝ) * 3 ^ 22 :=
          mul_le_mul_of_nonneg_left (le_trans hb_ex ha2) S_nat_pos.le
        linarith
      exact ⟨he_k2, hmag_k2⟩
  intro n hn
  by_cases hn94 : n ≤ 94
  · exact (hpair n hn94).1
  · have hn95 : n = 95 := by omega
    subst hn95
    exact (hpair 94 (by norm_num)).2

lemma sumBTree_approx_part {bt : BTree} {ω : ℝ} (hω : |ω| ≤ 19)
    {termFn : ℕ → ℕ → ℕ} {coeff : ℕ → ℝ}
    (hshape : checkBShape bt 0 96 = true)
    (hb : ∀ n < 96,
      |valZ Z_nat (btreeGet bt 0 96 n) - (S_nat : ℝ) * bEx ω n| ≤ uSeq n ∧
      |valZ Z_nat (btreeGet bt 0 96 n)| ≤ (S_nat : ℝ) * 3 ^ 22 + 20000 * 3 ^ 22)
    (hterm : ∀ n < 96, ∃ (neg : Bool) (num den : ℕ),
      0 < den ∧
      (∀ bn, termFn bn n = onatMulDiv Z_nat bn neg num den) ∧
      signB neg * (num : ℝ) / (den : ℝ) = coeff n ∧
      |coeff n| ≤ 8) :
    |valZ Z_nat (sumBTree Z_nat termFn bt 0 96) -
      (S_nat : ℝ) * ∑ n ∈ Finset.range 96, bEx ω n * coeff n| ≤ E_SUM := by
  let M : ℕ → ℝ := fun n => 8 * ((S_nat : ℝ) * aMaj n + uSeq n)
  have hM_nn : ∀ n ∈ Finset.Ico 0 96, 0 ≤ M n := fun n _ => by
    dsimp [M]
    exact mul_nonneg (by norm_num) (add_nonneg (mul_nonneg S_nat_pos.le (aMaj_nonneg n)) (uSeq_nonneg n))
  have hnum_over_den : ∀ n (hn : n < 96) (neg : Bool) (num den : ℕ),
      0 < den → signB neg * (num : ℝ) / (den : ℝ) = coeff n → |coeff n| ≤ 8 →
      (num : ℝ) / (den : ℝ) ≤ 8 := by
    intro n _ neg num den hden hceq hcle
    have : |signB neg * (num : ℝ) / (den : ℝ)| = (num : ℝ) / (den : ℝ) := by
      rw [abs_div, abs_mul, abs_signB, one_mul,
        abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos (Nat.cast_pos.mpr hden)]
    rw [hceq] at this
    linarith
  have hterm_each : ∀ n < 96,
      |valZ Z_nat (termFn (btreeGet bt 0 96 n) n) - (S_nat : ℝ) * (bEx ω n * coeff n)| ≤
        1 + 8 * uSeq n ∧
      |valZ Z_nat (termFn (btreeGet bt 0 96 n) n)| ≤ M n := by
    intro n hn
    obtain ⟨neg, num, den, hden, hfn, hceq, hcle⟩ := hterm n hn
    obtain ⟨hbn_err, _⟩ := hb n hn
    have hnd_le8 := hnum_over_den n hn neg num den hden hceq hcle
    have hbn_pt : |valZ Z_nat (btreeGet bt 0 96 n)| ≤ (S_nat : ℝ) * aMaj n + uSeq n := by
      have hb_ex := (aMaj_nonneg_and_bEx_le hω n).1.2
      have htri := abs_le_abs_add_err (valZ Z_nat (btreeGet bt 0 96 n)) ((S_nat : ℝ) * bEx ω n)
      rw [abs_mul, abs_of_pos S_nat_pos] at htri
      have hS : (S_nat : ℝ) * |bEx ω n| ≤ (S_nat : ℝ) * aMaj n :=
        mul_le_mul_of_nonneg_left hb_ex S_nat_pos.le
      linarith
    have hmag_leM : |valZ Z_nat (btreeGet bt 0 96 n)| * (num : ℝ) / (den : ℝ) ≤ M n := by
      rw [mul_div_assoc]; dsimp [M]
      calc
        |valZ Z_nat (btreeGet bt 0 96 n)| * ((num : ℝ) / (den : ℝ))
          ≤ ((S_nat : ℝ) * aMaj n + uSeq n) * 8 :=
            mul_le_mul hbn_pt hnd_le8 (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
              (add_nonneg (mul_nonneg S_nat_pos.le (aMaj_nonneg n)) (uSeq_nonneg n))
        _ = 8 * ((S_nat : ℝ) * aMaj n + uSeq n) := by ring
    have hMZ : M n ≤ (Z_nat : ℝ) := by
      dsimp [M]
      have ha := aMaj_le_3_pow_22 n hn
      have hu := uPoly_95_one_le.2.2 n hn
      have hS : (S_nat : ℝ) * aMaj n ≤ (S_nat : ℝ) * 3 ^ 22 :=
        mul_le_mul_of_nonneg_left ha S_nat_pos.le
      linarith [sumM_bound_le_Z_div_2, Z_nat_pos]
    rw [hfn]
    obtain ⟨herr_div, hmag_div⟩ := valZ_onatMulDiv_approx neg hden (le_trans hmag_leM hMZ)
    refine ⟨?_, le_trans hmag_div hmag_leM⟩
    have hid : signB neg * valZ Z_nat (btreeGet bt 0 96 n) * (num : ℝ) / (den : ℝ) =
        valZ Z_nat (btreeGet bt 0 96 n) * coeff n := by
      rw [← hceq]; ring
    rw [hid] at herr_div
    have hsplit : valZ Z_nat (onatMulDiv Z_nat (btreeGet bt 0 96 n) neg num den) -
        (S_nat : ℝ) * (bEx ω n * coeff n) =
      (valZ Z_nat (onatMulDiv Z_nat (btreeGet bt 0 96 n) neg num den) -
        valZ Z_nat (btreeGet bt 0 96 n) * coeff n) +
      (valZ Z_nat (btreeGet bt 0 96 n) - (S_nat : ℝ) * bEx ω n) * coeff n := by ring
    rw [hsplit]
    have hmul_err : |(valZ Z_nat (btreeGet bt 0 96 n) - (S_nat : ℝ) * bEx ω n) * coeff n| ≤ 8 * uSeq n := by
      rw [abs_mul, mul_comm]
      exact mul_le_mul hcle hbn_err (abs_nonneg _) (by norm_num)
    exact le_trans (abs_add_le _ _) (add_le_add herr_div hmul_err)
  obtain ⟨_, _, hm1⟩ := aMaj_95_96_bounds
  obtain ⟨_, hu_sum_le, _⟩ := uPoly_95_one_le
  have hmaj_sum : ∑ n ∈ Finset.Ico 0 96, aMaj n = majPoly 95 1 := by
    have hgen : ∀ m : ℕ, majPoly m 1 = ∑ k ∈ Finset.range (m + 1), aMaj k := by
      intro m; induction m with
      | zero => simp [majPoly, aMaj, bEx]
      | succ k ih => rw [Finset.sum_range_succ, ← ih]; simp [majPoly]
    rw [Nat.Ico_zero_eq_range, ← hgen 95]
  have hsumM_le : (∑ n ∈ Finset.Ico 0 96, M n) ≤ (Z_nat : ℝ) / 2 := by
    dsimp [M]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, hmaj_sum]
    have hS : (S_nat : ℝ) * majPoly 95 1 ≤ (S_nat : ℝ) * 3 ^ 22 :=
      mul_le_mul_of_nonneg_left hm1 S_nat_pos.le
    linarith [sumM_bound_le_Z_div_2]
  obtain ⟨hsum_eq, _⟩ := sumBTree_eq_sum hM_nn hshape
    (fun n hn => (hterm_each n (Finset.mem_Ico.mp hn).2).2) hsumM_le
  rw [hsum_eq, Nat.Ico_zero_eq_range, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hsum_abs : |∑ n ∈ Finset.range 96,
      (valZ Z_nat (termFn (btreeGet bt 0 96 n) n) - (S_nat : ℝ) * (bEx ω n * coeff n))| ≤
      ∑ n ∈ Finset.range 96, (1 + 8 * uSeq n) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact Finset.sum_le_sum fun n hn => (hterm_each n (Finset.mem_range.mp hn)).1
  have hrhs_eq : (∑ n ∈ Finset.range 96, (1 + 8 * uSeq n)) = 96 + 8 * ∑ n ∈ Finset.Ico 0 96, uSeq n := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.mul_sum, ← Nat.Ico_zero_eq_range]
    norm_num
  linarith [sum_err_96_le_E_SUM]

end
end GaussSmallBridge

namespace GaussSmallBridge

/-! ### Part 4B-3: Checker Tree Functions and Complete Soundness Proof -/

def checkQTree (s z errTI errT2I shD denLo baseErrD v0r v0i vtr vti vt2r vt2i : Nat) :
    QTree → Bool → Nat → Nat → Bool
  | .Q up udp uvt2, hNeg, hAbs, hQ =>
    let shH := Nat.pow 2 hQ
    let shH2 := Nat.mul shH shH
    let hAbs2 := Nat.mul hAbs hAbs
    let pr := onatAdd z (onatAdd z v0r (onatMulDiv z vtr hNeg hAbs shH)) (onatMulDiv z vt2r false hAbs2 shH2)
    let pi := onatAdd z (onatAdd z v0i (onatMulDiv z vti hNeg hAbs shH)) (onatMulDiv z vt2i false hAbs2 shH2)
    let dpr := onatAdd z vtr (onatMulDiv z vt2r hNeg (Nat.mul 2 hAbs) shH)
    let dpi := onatAdd z vti (onatMulDiv z vt2i hNeg (Nat.mul 2 hAbs) shH)
    let apr := Nat.add (onatAbs z pr) 18014398509481984
    let api := Nat.add (onatAbs z pi) 18014398509481984
    let adpr := Nat.add (onatAbs z dpr) 18014398509481984
    let adpi := Nat.add (onatAbs z dpi) 18014398509481984
    let avt2r := Nat.add (onatAbs z vt2r) 18014398509481984
    let avt2i := Nat.add (onatAbs z vt2i) 18014398509481984
    let ok1 := Nat.ble (Nat.add (Nat.mul apr apr) (Nat.mul api api)) (Nat.mul up up)
    let ok2 := Nat.ble (Nat.add (Nat.mul adpr adpr) (Nat.mul adpi adpi)) (Nat.mul udp udp)
    let ok3 := Nat.ble (Nat.add (Nat.mul avt2r avt2r) (Nat.mul avt2i avt2i)) (Nat.mul uvt2 uvt2)
    let htMax := Nat.add hAbs 1
    let shH3 := Nat.mul shH2 shH
    let errHt :=
      Nat.add (Nat.add (Nat.div (Nat.mul errTI htMax) shH) 1)
        (Nat.add (Nat.add (Nat.div (Nat.mul errT2I (Nat.mul htMax htMax)) shH2) 1)
          (Nat.add (Nat.add (Nat.div (Nat.mul (Nat.mul 10 s) htMax) (Nat.mul shH shD)) 1)
            (Nat.add (Nat.div (Nat.mul (Nat.mul 16 s) (Nat.mul htMax (Nat.mul htMax htMax))) shH3) 1)))
    let numUp :=
      Nat.add baseErrD
        (Nat.add up
          (Nat.add (Nat.add (Nat.div udp shH) 1)
            (Nat.add (Nat.add (Nat.div uvt2 shH2) 1) errHt)))
    let okHt := Nat.ble htMax shH
    Bool.and okHt (Bool.and ok1 (Bool.and ok2 (Bool.and ok3 (Nat.ble (Nat.mul 2 numUp) (Nat.mul 3 denLo)))))
  | .Z l r, _, hAbs, hQ =>
    let hQ1 := Nat.add hQ 1
    Bool.and (Nat.beq hAbs 0)
      (Bool.and
        (checkQTree s z errTI errT2I shD denLo baseErrD v0r v0i vtr vti vt2r vt2i l true 1 hQ1)
        (checkQTree s z errTI errT2I shD denLo baseErrD v0r v0i vtr vti vt2r vt2i r false 1 hQ1))
  | .S l r, hNeg, hAbs, hQ =>
    let hQ1 := Nat.add hQ 1
    let aLo := if hNeg then Nat.add (Nat.mul 2 hAbs) 1 else Nat.sub (Nat.mul 2 hAbs) 1
    let aHi := if hNeg then Nat.sub (Nat.mul 2 hAbs) 1 else Nat.add (Nat.mul 2 hAbs) 1
    Bool.and (Nat.ble 1 hAbs)
      (Bool.and
        (checkQTree s z errTI errT2I shD denLo baseErrD v0r v0i vtr vti vt2r vt2i l hNeg aLo hQ1)
        (checkQTree s z errTI errT2I shD denLo baseErrD v0r v0i vtr vti vt2r vt2i r hNeg aHi hQ1))

def checkStrip (s z w6Hi err0I errDI errTI errT2I shD shD2 denLo : Nat) (bt : BTree)
    (p : Nat) : StripCert → Bool
  | .M v0r v0i vdr vdi vtr vti vt2r vt2i udMSum qt =>
    let fourP2 := Nat.mul 4 (Nat.mul p p)
    let okSums :=
      Bool.and (Nat.beq v0r (sumBTree z (term0R z p 16 fourP2) bt 0 96))
      (Bool.and (Nat.beq v0i (sumBTree z (term0I z p 16 fourP2) bt 0 96))
      (Bool.and (Nat.beq vdr (sumBTree z (termDR z p 16 fourP2) bt 0 96))
      (Bool.and (Nat.beq vdi (sumBTree z (termDI z p 16 fourP2) bt 0 96))
      (Bool.and (Nat.beq vtr (sumBTree z (termTR z p 16 fourP2 1024) bt 0 96))
      (Bool.and (Nat.beq vti (sumBTree z (termTI z p 16 fourP2 1024) bt 0 96))
      (Bool.and (Nat.beq vt2r (sumBTree z (termT2R z p 16 fourP2 32768) bt 0 96))
                (Nat.beq vt2i (sumBTree z (termT2I z p 16 fourP2 32768) bt 0 96))))))))
    let avdr := Nat.add (onatAbs z vdr) 18014398509481984
    let avdi := Nat.add (onatAbs z vdi) 18014398509481984
    let okUd := Nat.ble (Nat.add (Nat.mul avdr avdr) (Nat.mul avdi avdi)) (Nat.mul udMSum udMSum)
    let udM := Nat.add (Nat.div (Nat.mul w6Hi udMSum) s) 1
    let baseErrD :=
      Nat.add err0I
        (Nat.add (Nat.add (Nat.div (Nat.add udM errDI) shD) 1)
          (Nat.add (Nat.div (Nat.mul 40 s) shD2) 1))
    Bool.and okSums (Bool.and okUd (checkQTree s z errTI errT2I shD denLo baseErrD v0r v0i vtr vti vt2r vt2i qt false 0 4))

def checkFastDTree (s z pi0Den w6Num w6Hi err0I errDI errTI errT2I : Nat) (dNeg : Bool) :
    FastDTree → Nat → Nat → Bool
  | .dleaf bt dv0r dv0i dvdr dvdi lDen udDenSum s17 s19 s21 s23, kAbs, qD =>
    let dNum := Nat.add (Nat.mul 2 kAbs) 1
    let dq1 := Nat.add qD 1
    let shD := Nat.pow 2 dq1
    let shD2 := Nat.mul shD shD
    let denBase := Nat.mul pi0Den shD
    let numW := Nat.mul w6Num dNum
    let okDenSums :=
      Bool.and (Nat.beq dv0r (sumBTree z (term0R z 1 1 4) bt 0 96))
      (Bool.and (Nat.beq dv0i (sumBTree z (term0I z 1 1 4) bt 0 96))
      (Bool.and (Nat.beq dvdr (sumBTree z (termDR z 1 1 4) bt 0 96))
                (Nat.beq dvdi (sumBTree z (termDI z 1 1 4) bt 0 96))))
    if Bool.and (checkBTree s z denBase numW dNeg bt) okDenSums then
      let rLo := Nat.sub (onatAbs z dv0r) 18014398509481984
      let iLo := Nat.sub (onatAbs z dv0i) 18014398509481984
      let okL := Nat.ble (Nat.mul lDen lDen) (Nat.add (Nat.mul rLo rLo) (Nat.mul iLo iLo))
      let avdr := Nat.add (onatAbs z dvdr) 18014398509481984
      let avdi := Nat.add (onatAbs z dvdi) 18014398509481984
      let okUd := Nat.ble (Nat.add (Nat.mul avdr avdr) (Nat.mul avdi avdi)) (Nat.mul udDenSum udDenSum)
      let udDen := Nat.add (Nat.div (Nat.mul w6Hi udDenSum) s) 1
      let subDen :=
        Nat.add (Nat.add (Nat.div (Nat.add udDen errDI) shD) 1)
          (Nat.add err0I (Nat.add (Nat.div (Nat.mul 40 s) shD2) 1))
      if Bool.and okL (Bool.and okUd (Nat.ble (Nat.add subDen 1) lDen)) then
        let denLo := Nat.sub lDen subDen
        Bool.and (checkStrip s z w6Hi err0I errDI errTI errT2I shD shD2 denLo bt 17 s17)
        (Bool.and (checkStrip s z w6Hi err0I errDI errTI errT2I shD shD2 denLo bt 19 s19)
        (Bool.and (checkStrip s z w6Hi err0I errDI errTI errT2I shD shD2 denLo bt 21 s21)
                  (checkStrip s z w6Hi err0I errDI errTI errT2I shD shD2 denLo bt 23 s23)))
      else false
    else false
  | .dsplit l r, kAbs, qD =>
    let qD1 := Nat.add qD 1
    Bool.and
      (checkFastDTree s z pi0Den w6Num w6Hi err0I errDI errTI errT2I dNeg l (Nat.mul 2 kAbs) qD1)
      (checkFastDTree s z pi0Den w6Num w6Hi err0I errDI errTI errT2I dNeg r (Nat.add (Nat.mul 2 kAbs) 1) qD1)

noncomputable section

private lemma nat_div_add_one_ge (a b : ℕ) (hb : 0 < b) :
    (a : ℝ) / (b : ℝ) ≤ ((a / b + 1 : ℕ) : ℝ) := by
  have hbR : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb
  rw [div_le_iff₀ hbR]
  have hlt : a < (a / b + 1) * b := by
    have h1 := Nat.div_add_mod a b
    have h2 := Nat.mod_lt a hb
    calc
      a = b * (a / b) + a % b := h1.symm
      _ < b * (a / b) + b := Nat.add_lt_add_left h2 _
      _ = (a / b + 1) * b := by ring
  exact_mod_cast hlt.le

private lemma norm_complex_le_of_re_im_sq {w : ℂ} {ar ai u : ℝ}
    (har : |w.re| ≤ ar) (hai : |w.im| ≤ ai) (hu : 0 ≤ u) (hsq : ar ^ 2 + ai ^ 2 ≤ u ^ 2) :
    ‖w‖ ≤ u := by
  have hw2 : ‖w‖ ^ 2 ≤ u ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hr2 : w.re * w.re ≤ ar ^ 2 := by
      have : |w.re| ^ 2 ≤ ar ^ 2 := pow_le_pow_left₀ (abs_nonneg _) har 2
      rwa [sq_abs, sq] at this
    have hi2 : w.im * w.im ≤ ai ^ 2 := by
      have : |w.im| ^ 2 ≤ ai ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hai 2
      rwa [sq_abs, sq] at this
    linarith
  nlinarith [norm_nonneg w]

private lemma norm_complex_ge_of_re_im_sq {w : ℂ} {lr li l : ℝ}
    (hlr : 0 ≤ lr) (hli : 0 ≤ li) (hr : lr ≤ |w.re|) (hi : li ≤ |w.im|)
    (_hl : 0 ≤ l) (hsq : l ^ 2 ≤ lr ^ 2 + li ^ 2) :
    l ≤ ‖w‖ := by
  have hw2 : l ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hr2 : lr ^ 2 ≤ w.re * w.re := by
      have : lr ^ 2 ≤ |w.re| ^ 2 := pow_le_pow_left₀ hlr hr 2
      rw [sq_abs] at this; nlinarith [this]
    have hi2 : li ^ 2 ≤ w.im * w.im := by
      have : li ^ 2 ≤ |w.im| ^ 2 := pow_le_pow_left₀ hli hi 2
      rw [sq_abs] at this; nlinarith [this]
    linarith
  nlinarith [norm_nonneg w]

private lemma signed_nat_sub_eq (pos negP scale : ℕ) :
    let isNeg := Bool.not (Nat.ble negP pos)
    let mag := if isNeg then Nat.mul scale (Nat.sub negP pos) else Nat.mul scale (Nat.sub pos negP)
    signB isNeg * (mag : ℝ) = (scale : ℝ) * ((pos : ℝ) - (negP : ℝ)) := by
  simp only [Nat.mul_eq, Nat.sub_eq]
  by_cases h : negP ≤ pos
  · have hb : Nat.ble negP pos = true := Nat.ble_eq.mpr h
    simp [hb, signB, Nat.cast_sub h]
  · have hb : Nat.ble negP pos = false := Bool.eq_false_iff.mpr fun ht => h (Nat.ble_eq.mp ht)
    have hlt : pos ≤ negP := le_of_not_ge h
    simp [hb, signB, Nat.cast_sub hlt]
    ring

private lemma I_pow_mul_re_im (n : ℕ) (x y : ℝ) :
    let cNeg := Nat.ble 2 (n % 4)
    let cOdd := Nat.beq ((n % 4) % 2) 1
    (Complex.I ^ n * ((x : ℂ) + (y : ℂ) * Complex.I)).re =
      (if cOdd then -signB cNeg * y else signB cNeg * x) ∧
    (Complex.I ^ n * ((x : ℂ) + (y : ℂ) * Complex.I)).im =
      (if cOdd then signB cNeg * x else signB cNeg * y) := by
  have hdiv := (Nat.div_add_mod n 4).symm
  have hI4 : Complex.I ^ n = Complex.I ^ (n % 4) := by
    conv_lhs => rw [hdiv, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]
  rw [hI4]
  have hm : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hm with h | h | h | h <;> rw [h] <;> simp [signB, pow_succ]

private lemma z_powers_re_im {p P u : ℕ} (hP : 0 < P) (huP : P ≤ u) {z : ℂ}
    (hz : z = (u : ℂ) / (2 * (P : ℂ)) - ((p : ℝ) / (P : ℝ) : ℂ) * Complex.I) :
    let D : ℕ := u * u + 4 * p * p
    let a : ℝ := (2 * P * u : ℝ) / (D : ℝ)
    let b : ℝ := (4 * P * p : ℝ) / (D : ℝ)
    0 < D ∧ z ≠ 0 ∧ ‖1 / z‖ ≤ 2 ∧
    1 / z = (a : ℂ) + (b : ℂ) * Complex.I ∧
    -Complex.I / z ^ 2 = ((2 * a * b : ℝ) : ℂ) + ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * Complex.I ∧
    -1 / z ^ 3 = ((-(a ^ 3 - 3 * a * b ^ 2) : ℝ) : ℂ) + ((-(3 * a ^ 2 * b - b ^ 3) : ℝ) : ℂ) * Complex.I := by
  intro D a b
  have hu : 0 < u := lt_of_lt_of_le hP huP
  have hD : 0 < D := by dsimp [D]; positivity
  have hPR : (0 : ℝ) < (P : ℝ) := Nat.cast_pos.mpr hP
  have hDR : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD
  have hz_real : z = Complex.ofReal ((u : ℝ) / (2 * (P : ℝ))) - Complex.ofReal ((p : ℝ) / (P : ℝ)) * Complex.I := by
    rw [hz]; push_cast; rfl
  have hz_re : (1 / 2 : ℝ) ≤ z.re := by
    have hre : z.re = (u : ℝ) / (2 * (P : ℝ)) := by
      rw [hz_real]
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    rw [hre, div_le_div_iff₀ (by norm_num) (by positivity)]
    have : (P : ℝ) ≤ (u : ℝ) := Nat.cast_le.mpr huP
    linarith
  have hz_norm_ge : (1 / 2 : ℝ) ≤ ‖z‖ := le_trans hz_re (Complex.re_le_norm z)
  have hz_ne : z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hz_norm_ge; norm_num at hz_norm_ge
  have hinv_le : ‖1 / z‖ ≤ 2 := by
    rw [norm_div, norm_one, div_le_iff₀ (lt_of_lt_of_le (by norm_num) hz_norm_ge)]
    linarith
  have h1z : 1 / z = (a : ℂ) + (b : ℂ) * Complex.I := by
    rw [div_eq_iff hz_ne, hz_real]
    have hP_ne : (P : ℝ) ≠ 0 := hPR.ne'
    have hD_ne : (D : ℝ) ≠ 0 := hDR.ne'
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      dsimp only [a, b, D]
      field_simp [hP_ne, hD_ne]; push_cast; ring
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      dsimp only [a, b, D]
      field_simp [hP_ne, hD_ne]; push_cast; ring
  have h2z : -Complex.I / z ^ 2 = ((2 * a * b : ℝ) : ℂ) + ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * Complex.I := by
    have : -Complex.I / z ^ 2 = -Complex.I * (1 / z) ^ 2 := by ring
    rw [this, h1z]
    (apply Complex.ext <;> simp [sq]); ring
  have h3z : -1 / z ^ 3 = ((-(a ^ 3 - 3 * a * b ^ 2) : ℝ) : ℂ) + ((-(3 * a ^ 2 * b - b ^ 3) : ℝ) : ℂ) * Complex.I := by
    have : -1 / z ^ 3 = -(1 / z) ^ 3 := by ring
    rw [this, h1z]
    apply Complex.ext <;> simp [pow_succ] <;> ring
  exact ⟨hD, hz_ne, hinv_le, h1z, h2z, h3z⟩

private lemma poly_re_im_sum (ω : ℝ) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.range 96, Complex.I ^ n * (bEx ω n : ℂ) * f n).re =
      ∑ n ∈ Finset.range 96, bEx ω n * (Complex.I ^ n * f n).re ∧
    (∑ n ∈ Finset.range 96, Complex.I ^ n * (bEx ω n : ℂ) * f n).im =
      ∑ n ∈ Finset.range 96, bEx ω n * (Complex.I ^ n * f n).im := by
  rw [Complex.re_sum, Complex.im_sum]
  refine ⟨Finset.sum_congr rfl fun n _ => ?_, Finset.sum_congr rfl fun n _ => ?_⟩
  · have : Complex.I ^ n * (bEx ω n : ℂ) * f n = (bEx ω n : ℂ) * (Complex.I ^ n * f n) := by ring
    rw [this, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  · have : Complex.I ^ n * (bEx ω n : ℂ) * f n = (bEx ω n : ℂ) * (Complex.I ^ n * f n) := by ring
    rw [this, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

lemma all_strip_sums_sound {bt : BTree} {ω : ℝ} (hω : |ω| ≤ 19)
    (hshape : checkBShape bt 0 96 = true)
    (hb : ∀ n < 96,
      |valZ Z_nat (btreeGet bt 0 96 n) - (S_nat : ℝ) * bEx ω n| ≤ uSeq n ∧
      |valZ Z_nat (btreeGet bt 0 96 n)| ≤ (S_nat : ℝ) * 3 ^ 22 + 20000 * 3 ^ 22)
    (p P : ℕ) (hP : 0 < P) :
    let s₀ : ℂ := (1 / 2 : ℂ) + ((-(p : ℝ) / (P : ℝ) : ℝ) : ℂ) * Complex.I
    let fourP2 := 4 * (p * p)
    let fourCapP2 := 4 * (P * P)
    let eightCapP3 := 8 * (P * (P * P))
    |valZ Z_nat (sumBTree Z_nat (term0R Z_nat p P fourP2) bt 0 96) - (S_nat : ℝ) * (polyJ0 ω s₀).re| ≤ E_SUM ∧
    |valZ Z_nat (sumBTree Z_nat (term0I Z_nat p P fourP2) bt 0 96) - (S_nat : ℝ) * (polyJ0 ω s₀).im| ≤ E_SUM ∧
    |valZ Z_nat (sumBTree Z_nat (termDR Z_nat p P fourP2) bt 0 96) - (S_nat : ℝ) * (polyJdRaw ω s₀).re| ≤ E_SUM ∧
    |valZ Z_nat (sumBTree Z_nat (termDI Z_nat p P fourP2) bt 0 96) - (S_nat : ℝ) * (polyJdRaw ω s₀).im| ≤ E_SUM ∧
    |valZ Z_nat (sumBTree Z_nat (termTR Z_nat p P fourP2 fourCapP2) bt 0 96) - (S_nat : ℝ) * (polyJt ω s₀).re| ≤ E_SUM ∧
    |valZ Z_nat (sumBTree Z_nat (termTI Z_nat p P fourP2 fourCapP2) bt 0 96) - (S_nat : ℝ) * (polyJt ω s₀).im| ≤ E_SUM ∧
    |valZ Z_nat (sumBTree Z_nat (termT2R Z_nat p P fourP2 eightCapP3) bt 0 96) - (S_nat : ℝ) * (polyJt2 ω s₀).re| ≤ E_SUM ∧
    |valZ Z_nat (sumBTree Z_nat (termT2I Z_nat p P fourP2 eightCapP3) bt 0 96) - (S_nat : ℝ) * (polyJt2 ω s₀).im| ≤ E_SUM := by
  intro s₀ fourP2 fourCapP2 eightCapP3
  have hPR : (P : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Nat.cast_pos.mpr hP).ne'
  have hz0_eq : ∀ n : ℕ, s₀ + (n : ℂ) = (((2 * n + 1) * P : ℕ) : ℂ) / (2 * (P : ℂ)) - ((p : ℝ) / (P : ℝ) : ℂ) * Complex.I := by
    intro n; dsimp [s₀]; push_cast; field_simp [hPR]; ring
  have hzd_eq : ∀ n : ℕ, s₀ + (n : ℂ) + 1 = (((2 * n + 3) * P : ℕ) : ℂ) / (2 * (P : ℂ)) - ((p : ℝ) / (P : ℝ) : ℂ) * Complex.I := by
    intro n; dsimp [s₀]; push_cast; field_simp [hPR]; ring
  have norm_I_pow : ∀ (n : ℕ) (w : ℂ), ‖Complex.I ^ n * w‖ = ‖w‖ := fun n w => by
    rw [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
  have re_im_le8 : ∀ (n : ℕ) (w : ℂ), ‖w‖ ≤ 8 →
      |(Complex.I ^ n * w).re| ≤ 8 ∧ |(Complex.I ^ n * w).im| ≤ 8 := fun n w hw =>
    ⟨le_trans (Complex.abs_re_le_norm _) (by rw [norm_I_pow]; exact hw),
     le_trans (Complex.abs_im_le_norm _) (by rw [norm_I_pow]; exact hw)⟩
  unfold polyJ0 polyJdRaw polyJt polyJt2
  rw [(poly_re_im_sum ω _).1, (poly_re_im_sum ω _).2,
      (poly_re_im_sum ω _).1, (poly_re_im_sum ω _).2,
      (poly_re_im_sum ω _).1, (poly_re_im_sum ω _).2,
      (poly_re_im_sum ω _).1, (poly_re_im_sum ω _).2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 1. term0R
    refine sumBTree_approx_part hω hshape hb fun n _ => ?_
    have huP : P ≤ (2 * n + 1) * P := by nlinarith
    obtain ⟨hD, _, hinv2, h1z, _, _⟩ := z_powers_re_im hP huP (hz0_eq n)
    set u := (2 * n + 1) * P
    let cNeg := Nat.ble 2 (n % 4)
    let cOdd := Nat.beq ((n % 4) % 2) 1
    let D := u * u + fourP2
    have hD_eq : u * u + 4 * p * p = D := by dsimp [D, fourP2]; ring
    rw [hD_eq] at hD h1z
    refine ⟨if cOdd then Bool.not cNeg else cNeg,
      if cOdd then 4 * P * p else 2 * P * u, D, hD, ?_, ?_, ?_⟩
    · intro bn
      unfold term0R
      simp only [Nat.mul_eq, Nat.add_eq]
      change (if cOdd = true then _ else _) = onatMulDiv Z_nat bn (if cOdd = true then !cNeg else cNeg) (if cOdd = true then 4 * P * p else 2 * P * u) D
      cases cOdd <;> rfl
    · rw [h1z, (I_pow_mul_re_im n _ _).1]
      change signB (if cOdd = true then !cNeg else cNeg) * ↑(if cOdd = true then 4 * P * p else 2 * P * u) / ↑D =
        if cOdd = true then -signB cNeg * _ else signB cNeg * _
      cases cOdd <;> simp only [Bool.false_eq_true, ↓reduceIte, signB_not] <;> push_cast <;> ring
    · exact (re_im_le8 n _ (le_trans hinv2 (by norm_num))).1
  · -- 2. term0I
    refine sumBTree_approx_part hω hshape hb fun n _ => ?_
    have huP : P ≤ (2 * n + 1) * P := by nlinarith
    obtain ⟨hD, _, hinv2, h1z, _, _⟩ := z_powers_re_im hP huP (hz0_eq n)
    set u := (2 * n + 1) * P
    let cNeg := Nat.ble 2 (n % 4)
    let cOdd := Nat.beq ((n % 4) % 2) 1
    let D := u * u + fourP2
    have hD_eq : u * u + 4 * p * p = D := by dsimp [D, fourP2]; ring
    rw [hD_eq] at hD h1z
    refine ⟨cNeg, if cOdd then 2 * P * u else 4 * P * p, D, hD, ?_, ?_, ?_⟩
    · intro bn
      unfold term0I
      simp only [Nat.mul_eq, Nat.add_eq]
      change (if cOdd = true then _ else _) = onatMulDiv Z_nat bn cNeg (if cOdd = true then 2 * P * u else 4 * P * p) D
      cases cOdd <;> rfl
    · rw [h1z, (I_pow_mul_re_im n _ _).2]
      change signB cNeg * ↑(if cOdd = true then 2 * P * u else 4 * P * p) / ↑D =
        if cOdd = true then signB cNeg * _ else signB cNeg * _
      cases cOdd <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> push_cast <;> ring
    · exact (re_im_le8 n _ (le_trans hinv2 (by norm_num))).2
  · -- 3. termDR
    refine sumBTree_approx_part hω hshape hb fun n _ => ?_
    have huP : P ≤ (2 * n + 3) * P := by nlinarith
    obtain ⟨hD1, _, hinv2, h1z, _, _⟩ := z_powers_re_im hP huP (hzd_eq n)
    set u1 := (2 * n + 3) * P
    let cNeg := Nat.ble 2 (n % 4)
    let cOdd := Nat.beq ((n % 4) % 2) 1
    let D1 := u1 * u1 + fourP2
    have hD1_eq : u1 * u1 + 4 * p * p = D1 := by dsimp [D1, fourP2]; ring
    rw [hD1_eq] at hD1 h1z
    refine ⟨if cOdd then Bool.not cNeg else cNeg,
      if cOdd then 4 * P * p else 2 * P * u1, D1, hD1, ?_, ?_, ?_⟩
    · intro bn
      unfold termDR
      simp only [Nat.mul_eq, Nat.add_eq]
      change (if cOdd = true then _ else _) = onatMulDiv Z_nat bn (if cOdd = true then !cNeg else cNeg) (if cOdd = true then 4 * P * p else 2 * P * u1) D1
      cases cOdd <;> rfl
    · rw [h1z, (I_pow_mul_re_im n _ _).1]
      change signB (if cOdd = true then !cNeg else cNeg) * ↑(if cOdd = true then 4 * P * p else 2 * P * u1) / ↑D1 =
        if cOdd = true then -signB cNeg * _ else signB cNeg * _
      cases cOdd <;> simp only [Bool.false_eq_true, ↓reduceIte, signB_not] <;> push_cast <;> ring
    · exact (re_im_le8 n _ (le_trans hinv2 (by norm_num))).1
  · -- 4. termDI
    refine sumBTree_approx_part hω hshape hb fun n _ => ?_
    have huP : P ≤ (2 * n + 3) * P := by nlinarith
    obtain ⟨hD1, _, hinv2, h1z, _, _⟩ := z_powers_re_im hP huP (hzd_eq n)
    set u1 := (2 * n + 3) * P
    let cNeg := Nat.ble 2 (n % 4)
    let cOdd := Nat.beq ((n % 4) % 2) 1
    let D1 := u1 * u1 + fourP2
    have hD1_eq : u1 * u1 + 4 * p * p = D1 := by dsimp [D1, fourP2]; ring
    rw [hD1_eq] at hD1 h1z
    refine ⟨cNeg, if cOdd then 2 * P * u1 else 4 * P * p, D1, hD1, ?_, ?_, ?_⟩
    · intro bn
      unfold termDI
      simp only [Nat.mul_eq, Nat.add_eq]
      change (if cOdd = true then _ else _) = onatMulDiv Z_nat bn cNeg (if cOdd = true then 2 * P * u1 else 4 * P * p) D1
      cases cOdd <;> rfl
    · rw [h1z, (I_pow_mul_re_im n _ _).2]
      change signB cNeg * ↑(if cOdd = true then 2 * P * u1 else 4 * P * p) / ↑D1 =
        if cOdd = true then signB cNeg * _ else signB cNeg * _
      cases cOdd <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> push_cast <;> ring
    · exact (re_im_le8 n _ (le_trans hinv2 (by norm_num))).2
  · -- 5. termTR
    refine sumBTree_approx_part hω hshape hb fun n _ => ?_
    have huP : P ≤ (2 * n + 1) * P := by nlinarith
    obtain ⟨hD, _, hinv2, _, h2z, _⟩ := z_powers_re_im hP huP (hz0_eq n)
    set u := (2 * n + 1) * P
    let cNeg := Nat.ble 2 (n % 4)
    let cOdd := Nat.beq ((n % 4) % 2) 1
    let D := u * u + fourP2
    let D2 := D * D
    have hD_eq : u * u + 4 * p * p = D := by dsimp [D, fourP2]; ring
    rw [hD_eq] at hD h2z
    have hD2 : 0 < D2 := Nat.mul_pos hD hD
    have hsub := signed_nat_sub_eq (u * u) fourP2 fourCapP2
    dsimp only [Nat.mul_eq, Nat.sub_eq] at hsub
    set a2Neg := Bool.not (Nat.ble fourP2 (u * u))
    let a2Mag := if a2Neg then fourCapP2 * (fourP2 - u * u) else fourCapP2 * (u * u - fourP2)
    let b2Mag := 16 * (P * P) * (u * p)
    refine ⟨if cOdd then Bool.xor cNeg a2Neg else cNeg,
      if cOdd then a2Mag else b2Mag, D2, hD2, ?_, ?_, ?_⟩
    · intro bn
      unfold termTR
      simp only [Nat.mul_eq, Nat.add_eq, Nat.sub_eq]
      change (if cOdd = true then _ else _) = onatMulDiv Z_nat bn (if cOdd = true then Bool.xor cNeg a2Neg else cNeg) (if cOdd = true then a2Mag else b2Mag) D2
      cases cOdd <;> rfl
    · rw [h2z, (I_pow_mul_re_im n _ _).1]
      change signB (if cOdd = true then Bool.xor cNeg a2Neg else cNeg) * ↑(if cOdd = true then a2Mag else b2Mag) / ↑D2 =
        if cOdd = true then -signB cNeg * _ else signB cNeg * _
      have hDR : (D : ℝ) ≠ 0 := (Nat.cast_pos.mpr hD).ne'
      cases cOdd
      · simp only [Bool.false_eq_true, ↓reduceIte, b2Mag, D2]
        push_cast; field_simp [hDR]; ring
      · simp only [↓reduceIte, signB_xor, mul_assoc, a2Mag, hsub]
        dsimp only [fourCapP2, fourP2, D2]
        push_cast; field_simp [hDR]; ring
    · have hnorm4 : ‖-Complex.I / (s₀ + (n : ℂ)) ^ 2‖ ≤ 8 := by
        have : ‖-Complex.I / (s₀ + (n : ℂ)) ^ 2‖ = ‖1 / (s₀ + (n : ℂ))‖ ^ 2 := by
          rw [norm_div, norm_neg, Complex.norm_I, norm_pow, norm_div, norm_one, div_pow, one_pow]
        rw [this]; nlinarith [norm_nonneg (1 / (s₀ + (n : ℂ)))]
      exact (re_im_le8 n _ hnorm4).1
  · -- 6. termTI
    refine sumBTree_approx_part hω hshape hb fun n _ => ?_
    have huP : P ≤ (2 * n + 1) * P := by nlinarith
    obtain ⟨hD, _, hinv2, _, h2z, _⟩ := z_powers_re_im hP huP (hz0_eq n)
    set u := (2 * n + 1) * P
    let cNeg := Nat.ble 2 (n % 4)
    let cOdd := Nat.beq ((n % 4) % 2) 1
    let D := u * u + fourP2
    let D2 := D * D
    have hD_eq : u * u + 4 * p * p = D := by dsimp [D, fourP2]; ring
    rw [hD_eq] at hD h2z
    have hD2 : 0 < D2 := Nat.mul_pos hD hD
    have hsub := signed_nat_sub_eq (u * u) fourP2 fourCapP2
    dsimp only [Nat.mul_eq, Nat.sub_eq] at hsub
    set a2Neg := Bool.not (Nat.ble fourP2 (u * u))
    let a2Mag := if a2Neg then fourCapP2 * (fourP2 - u * u) else fourCapP2 * (u * u - fourP2)
    let b2Mag := 16 * (P * P) * (u * p)
    refine ⟨if cOdd then cNeg else Bool.xor cNeg (Bool.not a2Neg),
      if cOdd then b2Mag else a2Mag, D2, hD2, ?_, ?_, ?_⟩
    · intro bn
      unfold termTI
      simp only [Nat.mul_eq, Nat.add_eq, Nat.sub_eq]
      change (if cOdd = true then _ else _) = onatMulDiv Z_nat bn (if cOdd = true then cNeg else Bool.xor cNeg (!a2Neg)) (if cOdd = true then b2Mag else a2Mag) D2
      cases cOdd <;> rfl
    · rw [h2z, (I_pow_mul_re_im n _ _).2]
      change signB (if cOdd = true then cNeg else Bool.xor cNeg (!a2Neg)) * ↑(if cOdd = true then b2Mag else a2Mag) / ↑D2 =
        if cOdd = true then signB cNeg * _ else signB cNeg * _
      have hDR : (D : ℝ) ≠ 0 := (Nat.cast_pos.mpr hD).ne'
      cases cOdd
      · simp only [Bool.false_eq_true, ↓reduceIte, signB_xor, signB_not, a2Mag]
        have hsub' : (-signB a2Neg) * ((if a2Neg = true then fourCapP2 * (fourP2 - u * u) else fourCapP2 * (u * u - fourP2) : ℕ) : ℝ) =
            -(signB a2Neg * ((if a2Neg = true then fourCapP2 * (fourP2 - u * u) else fourCapP2 * (u * u - fourP2) : ℕ) : ℝ)) := by ring
        rw [mul_assoc, hsub', hsub]
        dsimp only [fourCapP2, fourP2, D2]
        push_cast; field_simp [hDR]; ring
      · simp only [↓reduceIte, b2Mag, D2]
        push_cast; field_simp [hDR]; ring
    · have hnorm4 : ‖-Complex.I / (s₀ + (n : ℂ)) ^ 2‖ ≤ 8 := by
        have : ‖-Complex.I / (s₀ + (n : ℂ)) ^ 2‖ = ‖1 / (s₀ + (n : ℂ))‖ ^ 2 := by
          rw [norm_div, norm_neg, Complex.norm_I, norm_pow, norm_div, norm_one, div_pow, one_pow]
        rw [this]; nlinarith [norm_nonneg (1 / (s₀ + (n : ℂ)))]
      exact (re_im_le8 n _ hnorm4).2
  · -- 7. termT2R
    refine sumBTree_approx_part hω hshape hb fun n _ => ?_
    have huP : P ≤ (2 * n + 1) * P := by nlinarith
    obtain ⟨hD, _, hinv2, _, _, h3z⟩ := z_powers_re_im hP huP (hz0_eq n)
    set u := (2 * n + 1) * P
    let cNeg := Nat.ble 2 (n % 4)
    let cOdd := Nat.beq ((n % 4) % 2) 1
    let nc := Bool.not cNeg
    let D := u * u + fourP2
    let D3 := (D * D) * D
    have hD_eq : u * u + 4 * p * p = D := by dsimp [D, fourP2]; ring
    rw [hD_eq] at hD h3z
    have hD3 : 0 < D3 := Nat.mul_pos (Nat.mul_pos hD hD) hD
    let re3Pos := u * (u * u)
    let re3NegP := 3 * u * fourP2
    have hsubA := signed_nat_sub_eq re3Pos re3NegP eightCapP3
    let im3Pos := 6 * (u * u) * p
    let im3NegP := 8 * (p * (p * p))
    have hsubB := signed_nat_sub_eq im3Pos im3NegP eightCapP3
    dsimp only [Nat.mul_eq, Nat.sub_eq] at hsubA hsubB
    set a3Neg := Bool.not (Nat.ble re3NegP re3Pos)
    set b3Neg := Bool.not (Nat.ble im3NegP im3Pos)
    let a3Mag := if a3Neg then eightCapP3 * (re3NegP - re3Pos) else eightCapP3 * (re3Pos - re3NegP)
    let b3Mag := if b3Neg then eightCapP3 * (im3NegP - im3Pos) else eightCapP3 * (im3Pos - im3NegP)
    refine ⟨if cOdd then Bool.xor (Bool.not nc) b3Neg else Bool.xor nc a3Neg,
      if cOdd then b3Mag else a3Mag, D3, hD3, ?_, ?_, ?_⟩
    · intro bn
      unfold termT2R
      simp only [Nat.mul_eq, Nat.add_eq, Nat.sub_eq]
      change (if cOdd = true then _ else _) = onatMulDiv Z_nat bn (if cOdd = true then Bool.xor (!nc) b3Neg else Bool.xor nc a3Neg) (if cOdd = true then b3Mag else a3Mag) D3
      cases cOdd <;> rfl
    · rw [h3z, (I_pow_mul_re_im n _ _).1]
      change signB (if cOdd = true then Bool.xor (!nc) b3Neg else Bool.xor nc a3Neg) * ↑(if cOdd = true then b3Mag else a3Mag) / ↑D3 =
        if cOdd = true then -signB cNeg * _ else signB cNeg * _
      have hDR : (D : ℝ) ≠ 0 := (Nat.cast_pos.mpr hD).ne'
      cases cOdd
      · simp only [Bool.false_eq_true, ↓reduceIte, signB_xor, signB_not, mul_assoc, nc, a3Mag, hsubA]
        dsimp only [re3Pos, re3NegP, eightCapP3, fourP2, D3]
        push_cast; field_simp [hDR]; ring
      · simp only [↓reduceIte, signB_xor, signB_not, neg_neg, mul_assoc, nc, b3Mag, hsubB]
        dsimp only [im3Pos, im3NegP, eightCapP3, D3]
        push_cast; field_simp [hDR]; ring
    · have hnorm8 : ‖-1 / (s₀ + (n : ℂ)) ^ 3‖ ≤ 8 := by
        have : ‖-1 / (s₀ + (n : ℂ)) ^ 3‖ = ‖1 / (s₀ + (n : ℂ))‖ ^ 3 := by
          rw [norm_div, norm_neg, norm_one, norm_pow, norm_div, norm_one, div_pow, one_pow]
        rw [this]
        exact le_trans (pow_le_pow_left₀ (norm_nonneg _) hinv2 3) (by norm_num)
      exact (re_im_le8 n _ hnorm8).1
  · -- 8. termT2I
    refine sumBTree_approx_part hω hshape hb fun n _ => ?_
    have huP : P ≤ (2 * n + 1) * P := by nlinarith
    obtain ⟨hD, _, hinv2, _, _, h3z⟩ := z_powers_re_im hP huP (hz0_eq n)
    set u := (2 * n + 1) * P
    let cNeg := Nat.ble 2 (n % 4)
    let cOdd := Nat.beq ((n % 4) % 2) 1
    let nc := Bool.not cNeg
    let D := u * u + fourP2
    let D3 := (D * D) * D
    have hD_eq : u * u + 4 * p * p = D := by dsimp [D, fourP2]; ring
    rw [hD_eq] at hD h3z
    have hD3 : 0 < D3 := Nat.mul_pos (Nat.mul_pos hD hD) hD
    let re3Pos := u * (u * u)
    let re3NegP := 3 * u * fourP2
    have hsubA := signed_nat_sub_eq re3Pos re3NegP eightCapP3
    let im3Pos := 6 * (u * u) * p
    let im3NegP := 8 * (p * (p * p))
    have hsubB := signed_nat_sub_eq im3Pos im3NegP eightCapP3
    dsimp only [Nat.mul_eq, Nat.sub_eq] at hsubA hsubB
    set a3Neg := Bool.not (Nat.ble re3NegP re3Pos)
    set b3Neg := Bool.not (Nat.ble im3NegP im3Pos)
    let a3Mag := if a3Neg then eightCapP3 * (re3NegP - re3Pos) else eightCapP3 * (re3Pos - re3NegP)
    let b3Mag := if b3Neg then eightCapP3 * (im3NegP - im3Pos) else eightCapP3 * (im3Pos - im3NegP)
    refine ⟨if cOdd then Bool.xor nc a3Neg else Bool.xor nc b3Neg,
      if cOdd then a3Mag else b3Mag, D3, hD3, ?_, ?_, ?_⟩
    · intro bn
      unfold termT2I
      simp only [Nat.mul_eq, Nat.add_eq, Nat.sub_eq]
      change (if cOdd = true then _ else _) = onatMulDiv Z_nat bn (if cOdd = true then Bool.xor nc a3Neg else Bool.xor nc b3Neg) (if cOdd = true then a3Mag else b3Mag) D3
      cases cOdd <;> rfl
    · rw [h3z, (I_pow_mul_re_im n _ _).2]
      change signB (if cOdd = true then Bool.xor nc a3Neg else Bool.xor nc b3Neg) * ↑(if cOdd = true then a3Mag else b3Mag) / ↑D3 =
        if cOdd = true then signB cNeg * _ else signB cNeg * _
      have hDR : (D : ℝ) ≠ 0 := (Nat.cast_pos.mpr hD).ne'
      cases cOdd
      · simp only [Bool.false_eq_true, ↓reduceIte, signB_xor, signB_not, mul_assoc, nc, b3Mag, hsubB]
        dsimp only [im3Pos, im3NegP, eightCapP3, D3]
        push_cast; field_simp [hDR]; ring
      · simp only [↓reduceIte, signB_xor, signB_not, mul_assoc, nc, a3Mag, hsubA]
        dsimp only [re3Pos, re3NegP, eightCapP3, fourP2, D3]
        push_cast; field_simp [hDR]; ring
    · have hnorm8 : ‖-1 / (s₀ + (n : ℂ)) ^ 3‖ ≤ 8 := by
        have : ‖-1 / (s₀ + (n : ℂ)) ^ 3‖ = ‖1 / (s₀ + (n : ℂ))‖ ^ 3 := by
          rw [norm_div, norm_neg, norm_one, norm_pow, norm_div, norm_one, div_pow, one_pow]
        rw [this]
        exact le_trans (pow_le_pow_left₀ (norm_nonneg _) hinv2 3) (by norm_num)
      exact (re_im_le8 n _ hnorm8).2

private lemma norm_polyJ_le {ω : ℝ} (hω : |ω| ≤ 19) (s₀ : ℂ) (hs₀ : (1 / 2 : ℝ) ≤ s₀.re) :
    ‖polyJ0 ω s₀‖ ≤ 8 * 3 ^ 22 ∧
    ‖polyJt ω s₀‖ ≤ 8 * 3 ^ 22 ∧
    ‖polyJt2 ω s₀‖ ≤ 8 * 3 ^ 22 := by
  unfold polyJ0 polyJt polyJt2
  obtain ⟨_, _, hm1⟩ := aMaj_95_96_bounds
  have hmaj_sum : ∑ n ∈ Finset.range 96, aMaj n = majPoly 95 1 := by
    have hgen : ∀ m : ℕ, majPoly m 1 = ∑ k ∈ Finset.range (m + 1), aMaj k := by
      intro m; induction m with
      | zero => simp [majPoly, aMaj, bEx]
      | succ k ih => rw [Finset.sum_range_succ, ← ih]; simp [majPoly]
    exact (hgen 95).symm
  have hinv_le : ∀ n : ℕ, ‖1 / (s₀ + (n : ℂ))‖ ≤ 2 := fun n => by
    have hre : (1 / 2 : ℝ) ≤ (s₀ + (n : ℂ)).re := by
      simp only [Complex.add_re, Complex.natCast_re]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hn_ge : (1 / 2 : ℝ) ≤ ‖s₀ + (n : ℂ)‖ := le_trans hre (Complex.re_le_norm _)
    rw [norm_div, norm_one, div_le_iff₀ (lt_of_lt_of_le (by norm_num) hn_ge)]
    linarith
  have bound_sum : ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 8) →
      ‖∑ n ∈ Finset.range 96, Complex.I ^ n * (bEx ω n : ℂ) * f n‖ ≤ 8 * 3 ^ 22 := by
    intro f hf
    calc
      ‖∑ n ∈ Finset.range 96, Complex.I ^ n * (bEx ω n : ℂ) * f n‖
        ≤ ∑ n ∈ Finset.range 96, ‖Complex.I ^ n * (bEx ω n : ℂ) * f n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range 96, 8 * aMaj n := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [norm_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul,
            Complex.norm_real, Real.norm_eq_abs, mul_comm]
          exact mul_le_mul (hf n) ((aMaj_nonneg_and_bEx_le hω n).1.2) (abs_nonneg _) (by norm_num)
      _ = 8 * ∑ n ∈ Finset.range 96, aMaj n := by rw [← Finset.mul_sum]
      _ = 8 * majPoly 95 1 := by rw [hmaj_sum]
      _ ≤ 8 * 3 ^ 22 := by linarith
  refine ⟨bound_sum _ fun n => le_trans (hinv_le n) (by norm_num),
    bound_sum _ fun n => ?_, bound_sum _ fun n => ?_⟩
  · have : ‖-Complex.I / (s₀ + (n : ℂ)) ^ 2‖ = ‖1 / (s₀ + (n : ℂ))‖ ^ 2 := by
      rw [norm_div, norm_neg, Complex.norm_I, norm_pow, norm_div, norm_one, div_pow, one_pow]
    rw [this]; nlinarith [hinv_le n, norm_nonneg (1 / (s₀ + (n : ℂ)))]
  · have : ‖-1 / (s₀ + (n : ℂ)) ^ 3‖ = ‖1 / (s₀ + (n : ℂ))‖ ^ 3 := by
      rw [norm_div, norm_neg, norm_one, norm_pow, norm_div, norm_one, div_pow, one_pow]
    rw [this]
    exact le_trans (pow_le_pow_left₀ (norm_nonneg _) (hinv_le n) 3) (by norm_num)

lemma checkQTree_sound {shD denLo baseErrD v0r v0i vtr vti vt2r vt2i : ℕ}
    {J0 Jt Jt2 : ℂ} {baseReal denReal hδ : ℝ}
    (hshD : 0 < shD)
    (hhδ : |hδ| ≤ 1 / (shD : ℝ))
    (hbase : baseReal ≤ (baseErrD : ℝ) / (S_nat : ℝ))
    (hden : (denLo : ℝ) / (S_nat : ℝ) ≤ denReal)
    (hv0r : |valZ Z_nat v0r - (S_nat : ℝ) * J0.re| ≤ E_SUM ∧ |valZ Z_nat v0r| ≤ (Z_nat : ℝ) / 4)
    (hv0i : |valZ Z_nat v0i - (S_nat : ℝ) * J0.im| ≤ E_SUM ∧ |valZ Z_nat v0i| ≤ (Z_nat : ℝ) / 4)
    (hvtr : |valZ Z_nat vtr - (S_nat : ℝ) * Jt.re| ≤ E_SUM ∧ |valZ Z_nat vtr| ≤ (Z_nat : ℝ) / 4)
    (hvti : |valZ Z_nat vti - (S_nat : ℝ) * Jt.im| ≤ E_SUM ∧ |valZ Z_nat vti| ≤ (Z_nat : ℝ) / 4)
    (hvt2r : |valZ Z_nat vt2r - (S_nat : ℝ) * Jt2.re| ≤ E_SUM ∧ |valZ Z_nat vt2r| ≤ (Z_nat : ℝ) / 4)
    (hvt2i : |valZ Z_nat vt2i - (S_nat : ℝ) * Jt2.im| ≤ E_SUM ∧ |valZ Z_nat vt2i| ≤ (Z_nat : ℝ) / 4)
    (qt : QTree) (hNeg : Bool) (hAbs hQ : ℕ)
    (hchk : checkQTree S_nat Z_nat ERRT_nat ERRT2_nat shD denLo baseErrD
      v0r v0i vtr vti vt2r vt2i qt hNeg hAbs hQ = true) :
    ∀ ht : ℝ, |ht - signB hNeg * (hAbs : ℝ) / ((2 ^ hQ : ℕ) : ℝ)| ≤ 1 / ((2 ^ hQ : ℕ) : ℝ) →
      2 * (baseReal + ‖J0 + (ht : ℂ) * Jt + ((ht ^ 2 : ℝ) : ℂ) * Jt2‖ +
        |ht| * (1 / 20000) + ht ^ 2 * (1 / 10000) + 10 * |ht| * |hδ| + 16 * |ht| ^ 3) ≤
        3 * denReal := by
  induction qt generalizing hNeg hAbs hQ with
  | Z l r ihl ihr =>
    simp only [checkQTree, Bool.and_eq_true, Nat.beq_eq, Nat.add_eq] at hchk
    obtain ⟨hhAbs0, hkl, hkr⟩ := hchk
    subst hhAbs0
    intro ht hht
    simp only [Nat.cast_zero, mul_zero, zero_div, sub_zero] at hht
    have hpow1 : ((2 ^ (hQ + 1) : ℕ) : ℝ) = 2 * ((2 ^ hQ : ℕ) : ℝ) := by
      rw [pow_succ, Nat.cast_mul, Nat.cast_ofNat]; ring
    have h2pos : (0 : ℝ) < ((2 ^ hQ : ℕ) : ℝ) := by positivity
    rcases le_total ht 0 with hle | hge
    · apply ihl true 1 (hQ + 1) hkl ht
      rw [hpow1]; simp only [signB, ↓reduceIte, Nat.cast_one, mul_one]
      have hht_lo := (abs_le.mp hht).1
      rw [abs_le]
      constructor
      · field_simp [h2pos.ne'] at hht_lo ⊢; nlinarith only [hle, hht_lo, h2pos]
      · field_simp [h2pos.ne'] at hht_lo ⊢; nlinarith only [hle, hht_lo, h2pos]
    · apply ihr false 1 (hQ + 1) hkr ht
      rw [hpow1]; simp only [signB, Bool.false_eq_true, ↓reduceIte, Nat.cast_one, mul_one]
      have hht_hi := (abs_le.mp hht).2
      rw [abs_le]
      constructor
      · field_simp [h2pos.ne'] at hht_hi ⊢; nlinarith only [hge, hht_hi, h2pos]
      · field_simp [h2pos.ne'] at hht_hi ⊢; nlinarith only [hge, hht_hi, h2pos]
  | S l r ihl ihr =>
    simp only [checkQTree, Bool.and_eq_true, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at hchk
    obtain ⟨hh1, hkl, hkr⟩ := hchk
    intro ht hht
    have hpow1 : ((2 ^ (hQ + 1) : ℕ) : ℝ) = 2 * ((2 ^ hQ : ℕ) : ℝ) := by
      rw [pow_succ, Nat.cast_mul, Nat.cast_ofNat]; ring
    have h2pos : (0 : ℝ) < ((2 ^ hQ : ℕ) : ℝ) := by positivity
    have hsub_cast : ((2 * hAbs - 1 : ℕ) : ℝ) = 2 * (hAbs : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    let htMid := signB hNeg * (hAbs : ℝ) / ((2 ^ hQ : ℕ) : ℝ)
    rcases le_total ht htMid with hle | hge
    · apply ihl hNeg (if hNeg then 2 * hAbs + 1 else 2 * hAbs - 1) (hQ + 1) hkl ht
      have hht_lo := (abs_le.mp hht).1
      cases hNeg
      · simp only [Bool.false_eq_true, ↓reduceIte, signB, htMid] at hle hht_lo ⊢
        rw [hpow1, hsub_cast, abs_le]
        constructor <;> { field_simp [h2pos.ne'] at hle hht_lo ⊢; nlinarith only [hle, hht_lo, h2pos] }
      · simp only [↓reduceIte, signB, htMid] at hle hht_lo ⊢
        rw [hpow1, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, abs_le]
        constructor <;> { field_simp [h2pos.ne'] at hle hht_lo ⊢; nlinarith only [hle, hht_lo, h2pos] }
    · apply ihr hNeg (if hNeg then 2 * hAbs - 1 else 2 * hAbs + 1) (hQ + 1) hkr ht
      have hht_hi := (abs_le.mp hht).2
      cases hNeg
      · simp only [Bool.false_eq_true, ↓reduceIte, signB, htMid] at hge hht_hi ⊢
        rw [hpow1, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, abs_le]
        constructor <;> { field_simp [h2pos.ne'] at hge hht_hi ⊢; nlinarith only [hge, hht_hi, h2pos] }
      · simp only [↓reduceIte, signB, htMid] at hge hht_hi ⊢
        rw [hpow1, hsub_cast, abs_le]
        constructor <;> { field_simp [h2pos.ne'] at hge hht_hi ⊢; nlinarith only [hge, hht_hi, h2pos] }
  | Q up udp uvt2 =>
    simp only [checkQTree, Bool.and_eq_true, Nat.ble_eq, Nat.pow_eq, Nat.mul_eq, Nat.add_eq, nat_div_def] at hchk
    rw [← PAD_nat_eq] at hchk
    obtain ⟨hokHt, hok1, hok2, hok3, hineq_nat⟩ := hchk
    intro ht hht
    set shH := 2 ^ hQ
    have hshH_pos : 0 < shH := Nat.pos_of_ne_zero (pow_ne_zero hQ (by norm_num))
    have hshHR_pos : (0 : ℝ) < (shH : ℝ) := Nat.cast_pos.mpr hshH_pos
    have hshH2_pos : 0 < shH * shH := Nat.mul_pos hshH_pos hshH_pos
    have hshH3_pos : 0 < shH * shH * shH := Nat.mul_pos hshH2_pos hshH_pos
    have hhAbs_le : (hAbs : ℝ) / (shH : ℝ) ≤ 1 := by
      rw [div_le_one hshHR_pos]; exact Nat.cast_le.mpr (by omega)
    have hhAbs2_le : ((hAbs * hAbs : ℕ) : ℝ) / ((shH * shH : ℕ) : ℝ) ≤ 1 := by
      have hshH2R_pos : (0 : ℝ) < (shH : ℝ) * (shH : ℝ) := mul_pos hshHR_pos hshHR_pos
      rw [Nat.cast_mul, Nat.cast_mul, div_le_one hshH2R_pos]
      have hle : hAbs ≤ shH := by omega
      exact_mod_cast Nat.mul_le_mul hle hle
    have h2hAbs_le : ((2 * hAbs : ℕ) : ℝ) / (shH : ℝ) ≤ 2 := by
      rw [Nat.cast_mul, Nat.cast_ofNat, div_le_iff₀ hshHR_pos]
      have : (hAbs : ℝ) ≤ (shH : ℝ) := Nat.cast_le.mpr (by omega)
      linarith only [this]
    let htMid : ℝ := signB hNeg * (hAbs : ℝ) / (shH : ℝ)
    have quad_pt : ∀ (v0 vt vt2 : ℕ) (c0 ct ct2 : ℝ),
        (|valZ Z_nat v0 - (S_nat : ℝ) * c0| ≤ E_SUM ∧ |valZ Z_nat v0| ≤ (Z_nat : ℝ) / 4) →
        (|valZ Z_nat vt - (S_nat : ℝ) * ct| ≤ E_SUM ∧ |valZ Z_nat vt| ≤ (Z_nat : ℝ) / 4) →
        (|valZ Z_nat vt2 - (S_nat : ℝ) * ct2| ≤ E_SUM ∧ |valZ Z_nat vt2| ≤ (Z_nat : ℝ) / 4) →
        |(S_nat : ℝ) * (c0 + htMid * ct + htMid ^ 2 * ct2)| ≤
          ((onatAbs Z_nat (onatAdd Z_nat (onatAdd Z_nat v0 (onatMulDiv Z_nat vt hNeg hAbs shH))
            (onatMulDiv Z_nat vt2 false (hAbs * hAbs) (shH * shH))) + PAD_nat : ℕ) : ℝ) ∧
        |(S_nat : ℝ) * (ct + 2 * htMid * ct2)| ≤
          ((onatAbs Z_nat (onatAdd Z_nat vt (onatMulDiv Z_nat vt2 hNeg (2 * hAbs) shH)) + PAD_nat : ℕ) : ℝ) := by
      intro v0 vt vt2 c0 ct ct2 ⟨he0, hm0⟩ ⟨het, hmt⟩ ⟨het2, hmt2⟩
      have hg_t : |valZ Z_nat vt| * (hAbs : ℝ) / (shH : ℝ) ≤ (Z_nat : ℝ) / 4 := by
        rw [mul_div_assoc]
        exact le_trans (mul_le_mul hmt hhAbs_le (div_nonneg (Nat.cast_nonneg _) hshHR_pos.le) (div_nonneg Z_nat_pos.le (by norm_num))) (mul_one _).le
      have hg_t2 : |valZ Z_nat vt2| * ((hAbs * hAbs : ℕ) : ℝ) / ((shH * shH : ℕ) : ℝ) ≤ (Z_nat : ℝ) / 4 := by
        rw [mul_div_assoc]
        exact le_trans (mul_le_mul hmt2 hhAbs2_le (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (div_nonneg Z_nat_pos.le (by norm_num))) (mul_one _).le
      have hg_dt : |valZ Z_nat vt2| * ((2 * hAbs : ℕ) : ℝ) / (shH : ℝ) ≤ (Z_nat : ℝ) / 2 := by
        rw [mul_div_assoc]
        exact le_trans (mul_le_mul hmt2 h2hAbs_le (div_nonneg (Nat.cast_nonneg _) hshHR_pos.le) (div_nonneg Z_nat_pos.le (by norm_num))) (by linarith only [Z_nat_pos])
      obtain ⟨her1, hmr1⟩ := valZ_onatMulDiv_approx hNeg hshH_pos (le_trans hg_t (by linarith only [Z_nat_pos]))
      obtain ⟨her2, hmr2⟩ := valZ_onatMulDiv_approx false hshH2_pos (le_trans hg_t2 (by linarith only [Z_nat_pos]))
      obtain ⟨her3, hmr3⟩ := valZ_onatMulDiv_approx hNeg hshH_pos (le_trans hg_dt (by linarith only [Z_nat_pos]))
      let t1 := onatMulDiv Z_nat vt hNeg hAbs shH
      let t2 := onatMulDiv Z_nat vt2 false (hAbs * hAbs) (shH * shH)
      let t3 := onatMulDiv Z_nat vt2 hNeg (2 * hAbs) shH
      have ha_0 : -(Z_nat : ℝ) / 2 ≤ valZ Z_nat v0 := by have := neg_abs_le (valZ Z_nat v0); linarith only [this, hm0, Z_nat_pos]
      have ha_t1 : -(Z_nat : ℝ) / 2 ≤ valZ Z_nat t1 := by
        have h1 := le_trans hmr1 hg_t
        have h2 := neg_abs_le (valZ Z_nat t1)
        linarith only [h1, h2, Z_nat_pos]
      have ha_01 : -(Z_nat : ℝ) / 2 ≤ valZ Z_nat (onatAdd Z_nat v0 t1) := by
        rw [valZ_onatAdd ha_0 ha_t1]
        have h1 := le_trans hmr1 hg_t
        have h2 := abs_add_le (valZ Z_nat v0) (valZ Z_nat t1)
        have h3 := neg_abs_le (valZ Z_nat v0 + valZ Z_nat t1)
        linarith only [hm0, h1, h2, h3]
      have ha_t2 : -(Z_nat : ℝ) / 2 ≤ valZ Z_nat t2 := by
        have h1 := le_trans hmr2 hg_t2
        have h2 := neg_abs_le (valZ Z_nat t2)
        linarith only [h1, h2, Z_nat_pos]
      have ha_vt : -(Z_nat : ℝ) / 2 ≤ valZ Z_nat vt := by have := neg_abs_le (valZ Z_nat vt); linarith only [this, hmt, Z_nat_pos]
      have ha_t3 : -(Z_nat : ℝ) / 2 ≤ valZ Z_nat t3 := by
        have h1 := le_trans hmr3 hg_dt
        have h2 := neg_abs_le (valZ Z_nat t3)
        linarith only [h1, h2]
      have hp_val : valZ Z_nat (onatAdd Z_nat (onatAdd Z_nat v0 t1) t2) = valZ Z_nat v0 + valZ Z_nat t1 + valZ Z_nat t2 := by
        rw [valZ_onatAdd ha_01 ha_t2, valZ_onatAdd ha_0 ha_t1]
      have hdp_val : valZ Z_nat (onatAdd Z_nat vt t3) = valZ Z_nat vt + valZ Z_nat t3 :=
        valZ_onatAdd ha_vt ha_t3
      have hhtMid_sq : signB false * valZ Z_nat vt2 * ((hAbs * hAbs : ℕ) : ℝ) / ((shH * shH : ℕ) : ℝ) =
          htMid ^ 2 * valZ Z_nat vt2 := by
        cases hNeg <;> { dsimp [signB, htMid]; push_cast; field_simp [hshHR_pos.ne'] }
      have hhtMid_1 : signB hNeg * valZ Z_nat vt * (hAbs : ℝ) / (shH : ℝ) = htMid * valZ Z_nat vt := by
        dsimp [htMid]; ring
      have hhtMid_2 : signB hNeg * valZ Z_nat vt2 * ((2 * hAbs : ℕ) : ℝ) / (shH : ℝ) = 2 * htMid * valZ Z_nat vt2 := by
        dsimp [htMid]; push_cast; ring
      rw [hhtMid_1] at her1
      rw [hhtMid_sq] at her2
      rw [hhtMid_2] at her3
      have hhm_abs : |htMid| ≤ 1 := by
        dsimp [htMid]; rw [abs_div, abs_mul, abs_signB, one_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos hshHR_pos]
        exact hhAbs_le
      have hhm2_abs : htMid ^ 2 ≤ 1 := by
        have := pow_le_pow_left₀ (abs_nonneg _) hhm_abs 2
        rwa [sq_abs, one_pow] at this
      have hp_err : |(valZ Z_nat v0 + valZ Z_nat t1 + valZ Z_nat t2) -
          (S_nat : ℝ) * (c0 + htMid * ct + htMid ^ 2 * ct2)| ≤ (PAD_nat : ℝ) := by
        have hsp : (valZ Z_nat v0 + valZ Z_nat t1 + valZ Z_nat t2) -
            (S_nat : ℝ) * (c0 + htMid * ct + htMid ^ 2 * ct2) =
          (valZ Z_nat v0 - (S_nat : ℝ) * c0) +
          (valZ Z_nat t1 - htMid * valZ Z_nat vt) +
          htMid * (valZ Z_nat vt - (S_nat : ℝ) * ct) +
          (valZ Z_nat t2 - htMid ^ 2 * valZ Z_nat vt2) +
          htMid ^ 2 * (valZ Z_nat vt2 - (S_nat : ℝ) * ct2) := by ring
        rw [hsp]
        have e1 : |htMid * (valZ Z_nat vt - (S_nat : ℝ) * ct)| ≤ E_SUM := by
          rw [abs_mul]; exact le_trans (mul_le_mul hhm_abs het (abs_nonneg _) zero_le_one) (one_mul _).le
        have e2 : |htMid ^ 2 * (valZ Z_nat vt2 - (S_nat : ℝ) * ct2)| ≤ E_SUM := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
          exact le_trans (mul_le_mul hhm2_abs het2 (abs_nonneg _) zero_le_one) (one_mul _).le
        have t_a := abs_add_le
          ((valZ Z_nat v0 - (S_nat : ℝ) * c0) + (valZ Z_nat t1 - htMid * valZ Z_nat vt) +
            htMid * (valZ Z_nat vt - (S_nat : ℝ) * ct) + (valZ Z_nat t2 - htMid ^ 2 * valZ Z_nat vt2))
          (htMid ^ 2 * (valZ Z_nat vt2 - (S_nat : ℝ) * ct2))
        have t_b := abs_add_le
          ((valZ Z_nat v0 - (S_nat : ℝ) * c0) + (valZ Z_nat t1 - htMid * valZ Z_nat vt) +
            htMid * (valZ Z_nat vt - (S_nat : ℝ) * ct))
          (valZ Z_nat t2 - htMid ^ 2 * valZ Z_nat vt2)
        have t_c := abs_add_le
          ((valZ Z_nat v0 - (S_nat : ℝ) * c0) + (valZ Z_nat t1 - htMid * valZ Z_nat vt))
          (htMid * (valZ Z_nat vt - (S_nat : ℝ) * ct))
        have t_d := abs_add_le (valZ Z_nat v0 - (S_nat : ℝ) * c0) (valZ Z_nat t1 - htMid * valZ Z_nat vt)
        linarith only [he0, her1, e1, her2, e2, t_a, t_b, t_c, t_d, three_E_SUM_add_two_le_PAD]
      have hdp_err : |(valZ Z_nat vt + valZ Z_nat t3) - (S_nat : ℝ) * (ct + 2 * htMid * ct2)| ≤ (PAD_nat : ℝ) := by
        have hsp : (valZ Z_nat vt + valZ Z_nat t3) - (S_nat : ℝ) * (ct + 2 * htMid * ct2) =
          (valZ Z_nat vt - (S_nat : ℝ) * ct) + (valZ Z_nat t3 - 2 * htMid * valZ Z_nat vt2) +
          (2 * htMid) * (valZ Z_nat vt2 - (S_nat : ℝ) * ct2) := by ring
        rw [hsp]
        have e3 : |(2 * htMid) * (valZ Z_nat vt2 - (S_nat : ℝ) * ct2)| ≤ 2 * E_SUM := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          have : 2 * |htMid| ≤ 2 := by linarith only [hhm_abs]
          exact mul_le_mul this het2 (abs_nonneg _) (by norm_num)
        have t_a := abs_add_le
          ((valZ Z_nat vt - (S_nat : ℝ) * ct) + (valZ Z_nat t3 - 2 * htMid * valZ Z_nat vt2))
          ((2 * htMid) * (valZ Z_nat vt2 - (S_nat : ℝ) * ct2))
        have t_b := abs_add_le (valZ Z_nat vt - (S_nat : ℝ) * ct) (valZ Z_nat t3 - 2 * htMid * valZ Z_nat vt2)
        linarith only [het, her3, e3, t_a, t_b, three_E_SUM_add_two_le_PAD]
      refine ⟨?_, ?_⟩
      · rw [Nat.cast_add, onatAbs_eq_abs, hp_val]
        have := abs_le_abs_add_err ((S_nat : ℝ) * (c0 + htMid * ct + htMid ^ 2 * ct2))
          (valZ Z_nat v0 + valZ Z_nat t1 + valZ Z_nat t2)
        rw [abs_sub_comm] at this
        linarith only [this, hp_err]
      · rw [Nat.cast_add, onatAbs_eq_abs, hdp_val]
        have := abs_le_abs_add_err ((S_nat : ℝ) * (ct + 2 * htMid * ct2)) (valZ Z_nat vt + valZ Z_nat t3)
        rw [abs_sub_comm] at this
        linarith only [this, hdp_err]
    obtain ⟨hpr_le, hdpr_le⟩ := quad_pt v0r vtr vt2r J0.re Jt.re Jt2.re hv0r hvtr hvt2r
    obtain ⟨hpi_le, hdpi_le⟩ := quad_pt v0i vti vt2i J0.im Jt.im Jt2.im hv0i hvti hvt2i
    let Pmid : ℂ := J0 + (htMid : ℂ) * Jt + ((htMid ^ 2 : ℝ) : ℂ) * Jt2
    let dPmid : ℂ := Jt + ((2 * htMid : ℝ) : ℂ) * Jt2
    have hSp_re : (((S_nat : ℝ) : ℂ) * Pmid).re = (S_nat : ℝ) * (J0.re + htMid * Jt.re + htMid ^ 2 * Jt2.re) := by
      simp only [Pmid, Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
    have hSp_im : (((S_nat : ℝ) : ℂ) * Pmid).im = (S_nat : ℝ) * (J0.im + htMid * Jt.im + htMid ^ 2 * Jt2.im) := by
      simp only [Pmid, Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero]
    have hSdp_re : (((S_nat : ℝ) : ℂ) * dPmid).re = (S_nat : ℝ) * (Jt.re + 2 * htMid * Jt2.re) := by
      simp only [dPmid, Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
    have hSdp_im : (((S_nat : ℝ) : ℂ) * dPmid).im = (S_nat : ℝ) * (Jt.im + 2 * htMid * Jt2.im) := by
      simp only [dPmid, Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero]
    rw [← hSp_re] at hpr_le
    rw [← hSp_im] at hpi_le
    rw [← hSdp_re] at hdpr_le
    rw [← hSdp_im] at hdpi_le
    have hSvt2_re : |(((S_nat : ℝ) : ℂ) * Jt2).re| ≤ ((onatAbs Z_nat vt2r + PAD_nat : ℕ) : ℝ) := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Nat.cast_add, onatAbs_eq_abs]
      have := abs_le_abs_add_err ((S_nat : ℝ) * Jt2.re) (valZ Z_nat vt2r)
      rw [abs_sub_comm] at this
      linarith [hvt2r.1, E_SUM_le_PAD]
    have hSvt2_im : |(((S_nat : ℝ) : ℂ) * Jt2).im| ≤ ((onatAbs Z_nat vt2i + PAD_nat : ℕ) : ℝ) := by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
        Nat.cast_add, onatAbs_eq_abs]
      have := abs_le_abs_add_err ((S_nat : ℝ) * Jt2.im) (valZ Z_nat vt2i)
      rw [abs_sub_comm] at this
      linarith [hvt2i.1, E_SUM_le_PAD]
    have hup_norm : (S_nat : ℝ) * ‖Pmid‖ ≤ (up : ℝ) := by
      have h1 : ‖((S_nat : ℝ) : ℂ) * Pmid‖ ≤ (up : ℝ) := by
        refine norm_complex_le_of_re_im_sq hpr_le hpi_le (Nat.cast_nonneg up) ?_
        rw [sq, sq, sq]; exact_mod_cast hok1
      rwa [norm_mul, Complex.norm_real, Real.norm_of_nonneg S_nat_pos.le] at h1
    have hudp_norm : (S_nat : ℝ) * ‖dPmid‖ ≤ (udp : ℝ) := by
      have h1 : ‖((S_nat : ℝ) : ℂ) * dPmid‖ ≤ (udp : ℝ) := by
        refine norm_complex_le_of_re_im_sq hdpr_le hdpi_le (Nat.cast_nonneg udp) ?_
        rw [sq, sq, sq]; exact_mod_cast hok2
      rwa [norm_mul, Complex.norm_real, Real.norm_of_nonneg S_nat_pos.le] at h1
    have huvt2_norm : (S_nat : ℝ) * ‖Jt2‖ ≤ (uvt2 : ℝ) := by
      have h1 : ‖((S_nat : ℝ) : ℂ) * Jt2‖ ≤ (uvt2 : ℝ) := by
        refine norm_complex_le_of_re_im_sq hSvt2_re hSvt2_im (Nat.cast_nonneg uvt2) ?_
        rw [sq, sq, sq]; exact_mod_cast hok3
      rwa [norm_mul, Complex.norm_real, Real.norm_of_nonneg S_nat_pos.le] at h1
    let δt : ℝ := ht - htMid
    have hδt_le : |δt| ≤ 1 / (shH : ℝ) := hht
    have hδt2_le : δt ^ 2 ≤ 1 / ((shH * shH : ℕ) : ℝ) := by
      have h1 : |δt| ^ 2 ≤ (1 / (shH : ℝ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hδt_le 2
      rw [sq_abs] at h1
      simpa [div_pow, sq] using h1
    have hpoly_id : J0 + (ht : ℂ) * Jt + ((ht ^ 2 : ℝ) : ℂ) * Jt2 =
        Pmid + (δt : ℂ) * dPmid + ((δt ^ 2 : ℝ) : ℂ) * Jt2 := by
      have hht_eq : ht = htMid + δt := by dsimp [δt]; ring
      dsimp [Pmid, dPmid]; rw [hht_eq]; push_cast; ring
    have hpoly_S : (S_nat : ℝ) * ‖J0 + (ht : ℂ) * Jt + ((ht ^ 2 : ℝ) : ℂ) * Jt2‖ ≤
        (up : ℝ) + ((udp / shH + 1 : ℕ) : ℝ) + ((uvt2 / (shH * shH) + 1 : ℕ) : ℝ) := by
      rw [hpoly_id]
      have ht_a := norm_add_le (Pmid + (δt : ℂ) * dPmid) (((δt ^ 2 : ℝ) : ℂ) * Jt2)
      have ht_b := norm_add_le Pmid ((δt : ℂ) * dPmid)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg δt)] at ht_a
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at ht_b
      have hterm_dp : (S_nat : ℝ) * (|δt| * ‖dPmid‖) ≤ ((udp / shH + 1 : ℕ) : ℝ) := by
        calc
          (S_nat : ℝ) * (|δt| * ‖dPmid‖) = |δt| * ((S_nat : ℝ) * ‖dPmid‖) := by ring
          _ ≤ (1 / (shH : ℝ)) * (udp : ℝ) :=
              mul_le_mul hδt_le hudp_norm (mul_nonneg S_nat_pos.le (norm_nonneg _)) (by positivity)
          _ = (udp : ℝ) / (shH : ℝ) := by ring
          _ ≤ ((udp / shH + 1 : ℕ) : ℝ) := nat_div_add_one_ge udp shH hshH_pos
      have hterm_vt2 : (S_nat : ℝ) * (δt ^ 2 * ‖Jt2‖) ≤ ((uvt2 / (shH * shH) + 1 : ℕ) : ℝ) := by
        calc
          (S_nat : ℝ) * (δt ^ 2 * ‖Jt2‖) = δt ^ 2 * ((S_nat : ℝ) * ‖Jt2‖) := by ring
          _ ≤ (1 / ((shH * shH : ℕ) : ℝ)) * (uvt2 : ℝ) :=
              mul_le_mul hδt2_le huvt2_norm (mul_nonneg S_nat_pos.le (norm_nonneg _)) (by positivity)
          _ = (uvt2 : ℝ) / ((shH * shH : ℕ) : ℝ) := by ring
          _ ≤ ((uvt2 / (shH * shH) + 1 : ℕ) : ℝ) := nat_div_add_one_ge uvt2 (shH * shH) hshH2_pos
      have htri_S : (S_nat : ℝ) * ‖Pmid + (δt : ℂ) * dPmid + ((δt ^ 2 : ℝ) : ℂ) * Jt2‖ ≤
          (S_nat : ℝ) * ‖Pmid‖ + (S_nat : ℝ) * (|δt| * ‖dPmid‖) + (S_nat : ℝ) * (δt ^ 2 * ‖Jt2‖) := by
        have htri_1 : ‖Pmid + (δt : ℂ) * dPmid + ((δt ^ 2 : ℝ) : ℂ) * Jt2‖ ≤
            ‖Pmid‖ + |δt| * ‖dPmid‖ + δt ^ 2 * ‖Jt2‖ := by linarith only [ht_a, ht_b]
        have htri_2 := mul_le_mul_of_nonneg_left htri_1 S_nat_pos.le
        linarith only [htri_2]
      linarith only [htri_S, hup_norm, hterm_dp, hterm_vt2]
    let htMax := hAbs + 1
    have hht_max : |ht| ≤ (htMax : ℝ) / (shH : ℝ) := by
      have h1 : |ht| ≤ |htMid| + |δt| := by
        have : ht = htMid + δt := by dsimp [δt]; ring
        rw [this]; exact abs_add_le _ _
      have h2 : |htMid| = (hAbs : ℝ) / (shH : ℝ) := by
        dsimp [htMid]; rw [abs_div, abs_mul, abs_signB, one_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos hshHR_pos]
      rw [h2] at h1
      calc |ht| ≤ (hAbs : ℝ) / (shH : ℝ) + 1 / (shH : ℝ) := by linarith only [h1, hδt_le]
        _ = (htMax : ℝ) / (shH : ℝ) := by dsimp [htMax]; push_cast; ring
    have hht2_max : ht ^ 2 ≤ ((htMax * htMax : ℕ) : ℝ) / ((shH * shH : ℕ) : ℝ) := by
      have h1 : |ht| ^ 2 ≤ ((htMax : ℝ) / (shH : ℝ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hht_max 2
      rw [sq_abs, div_pow] at h1
      simpa [sq] using h1
    have hht3_max : |ht| ^ 3 ≤ ((htMax * (htMax * htMax) : ℕ) : ℝ) / ((shH * shH * shH : ℕ) : ℝ) := by
      have h1 : |ht| ^ 3 ≤ ((htMax : ℝ) / (shH : ℝ)) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hht_max 3
      rw [div_pow] at h1
      simpa [pow_succ, sq, mul_assoc] using h1
    have herrT_S : (S_nat : ℝ) * (|ht| * (1 / 20000)) ≤ ((ERRT_nat * htMax / shH + 1 : ℕ) : ℝ) := by
      calc
        (S_nat : ℝ) * (|ht| * (1 / 20000)) = ((S_nat : ℝ) * (1 / 20000)) * |ht| := by ring
        _ ≤ (ERRT_nat : ℝ) * ((htMax : ℝ) / (shH : ℝ)) :=
            mul_le_mul S_errT_le hht_max (abs_nonneg _) (Nat.cast_nonneg _)
        _ = ((ERRT_nat * htMax : ℕ) : ℝ) / (shH : ℝ) := by push_cast; ring
        _ ≤ ((ERRT_nat * htMax / shH + 1 : ℕ) : ℝ) := nat_div_add_one_ge _ _ hshH_pos
    have herrT2_S : (S_nat : ℝ) * (ht ^ 2 * (1 / 10000)) ≤ ((ERRT2_nat * (htMax * htMax) / (shH * shH) + 1 : ℕ) : ℝ) := by
      calc
        (S_nat : ℝ) * (ht ^ 2 * (1 / 10000)) = ((S_nat : ℝ) * (1 / 10000)) * ht ^ 2 := by ring
        _ ≤ (ERRT2_nat : ℝ) * (((htMax * htMax : ℕ) : ℝ) / ((shH * shH : ℕ) : ℝ)) :=
            mul_le_mul S_errT2_le hht2_max (sq_nonneg _) (Nat.cast_nonneg _)
        _ = ((ERRT2_nat * (htMax * htMax) : ℕ) : ℝ) / ((shH * shH : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((ERRT2_nat * (htMax * htMax) / (shH * shH) + 1 : ℕ) : ℝ) := nat_div_add_one_ge _ _ hshH2_pos
    have herr10_S : (S_nat : ℝ) * (10 * |ht| * |hδ|) ≤ ((10 * S_nat * htMax / (shH * shD) + 1 : ℕ) : ℝ) := by
      have hprod : |ht| * |hδ| ≤ (htMax : ℝ) / ((shH * shD : ℕ) : ℝ) := by
        calc
          |ht| * |hδ| ≤ ((htMax : ℝ) / (shH : ℝ)) * (1 / (shD : ℝ)) :=
              mul_le_mul hht_max hhδ (abs_nonneg _) (by positivity)
          _ = (htMax : ℝ) / ((shH * shD : ℕ) : ℝ) := by push_cast; ring
      calc
        (S_nat : ℝ) * (10 * |ht| * |hδ|) = (10 * (S_nat : ℝ)) * (|ht| * |hδ|) := by ring
        _ ≤ (10 * (S_nat : ℝ)) * ((htMax : ℝ) / ((shH * shD : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hprod (mul_nonneg (by norm_num) S_nat_pos.le)
        _ = ((10 * S_nat * htMax : ℕ) : ℝ) / ((shH * shD : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((10 * S_nat * htMax / (shH * shD) + 1 : ℕ) : ℝ) := nat_div_add_one_ge _ _ (Nat.mul_pos hshH_pos hshD)
    have herr16_S : (S_nat : ℝ) * (16 * |ht| ^ 3) ≤ ((16 * S_nat * (htMax * (htMax * htMax)) / (shH * shH * shH) + 1 : ℕ) : ℝ) := by
      calc
        (S_nat : ℝ) * (16 * |ht| ^ 3) = (16 * (S_nat : ℝ)) * |ht| ^ 3 := by ring
        _ ≤ (16 * (S_nat : ℝ)) * (((htMax * (htMax * htMax) : ℕ) : ℝ) / ((shH * shH * shH : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hht3_max (mul_nonneg (by norm_num) S_nat_pos.le)
        _ = ((16 * S_nat * (htMax * (htMax * htMax)) : ℕ) : ℝ) / ((shH * shH * shH : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((16 * S_nat * (htMax * (htMax * htMax)) / (shH * shH * shH) + 1 : ℕ) : ℝ) := nat_div_add_one_ge _ _ hshH3_pos
    have hbase_S : (S_nat : ℝ) * baseReal ≤ (baseErrD : ℝ) := by
      have := (le_div_iff₀ S_nat_pos).mp hbase; linarith only [this]
    have hden_S : (denLo : ℝ) ≤ (S_nat : ℝ) * denReal := by
      have := (div_le_iff₀ S_nat_pos).mp hden; linarith only [this]
    have hineq_R : (2 : ℝ) *
        ((baseErrD : ℝ) + ((up : ℝ) + (((udp / shH + 1 : ℕ) : ℝ) +
          (((uvt2 / (shH * shH) + 1 : ℕ) : ℝ) +
            (((ERRT_nat * htMax / shH + 1 : ℕ) : ℝ) +
              (((ERRT2_nat * (htMax * htMax) / (shH * shH) + 1 : ℕ) : ℝ) +
                (((10 * S_nat * htMax / (shH * shD) + 1 : ℕ) : ℝ) +
                  ((16 * S_nat * (htMax * (htMax * htMax)) / (shH * shH * shH) + 1 : ℕ) : ℝ)))))))) ≤
        3 * (denLo : ℝ) := by
      exact_mod_cast hineq_nat
    have hS_comb : (S_nat : ℝ) *
        (2 * (baseReal + ‖J0 + (ht : ℂ) * Jt + ((ht ^ 2 : ℝ) : ℂ) * Jt2‖ +
          |ht| * (1 / 20000) + ht ^ 2 * (1 / 10000) + 10 * |ht| * |hδ| + 16 * |ht| ^ 3)) ≤
        (S_nat : ℝ) * (3 * denReal) := by
      linarith only [hbase_S, hpoly_S, herrT_S, herrT2_S, herr10_S, herr16_S, hineq_R, hden_S]
    exact le_of_mul_le_mul_left hS_comb S_nat_pos

lemma checkStrip_sound {bt : BTree} {δ₀ hδ denReal : ℝ} {shD denLo p : ℕ} {sc : StripCert}
    (hδ₀ : |δ₀| ≤ 1) (hshD : 0 < shD) (hhδ : |hδ| ≤ 1 / (shD : ℝ))
    (hden : (denLo : ℝ) / (S_nat : ℝ) ≤ denReal)
    (hden_val : Real.sqrt 3 * denReal ≤ ‖mellinVal (δ₀ + hδ) ((1 / 2 : ℂ) - Complex.I)‖)
    (hshape : checkBShape bt 0 96 = true)
    (hb : ∀ n < 96,
      |valZ Z_nat (btreeGet bt 0 96 n) - (S_nat : ℝ) * bEx (6 * pi0R * δ₀) n| ≤ uSeq n ∧
      |valZ Z_nat (btreeGet bt 0 96 n)| ≤ (S_nat : ℝ) * 3 ^ 22 + 20000 * 3 ^ 22)
    (hchk : checkStrip S_nat Z_nat W6_HI_nat ERR0_nat ERRD_nat ERRT_nat ERRT2_nat
      shD (shD * shD) denLo bt p sc = true) :
    ∀ t : ℝ, -(p : ℝ) / 16 - 1 / 16 ≤ t → t ≤ -(p : ℝ) / 16 + 1 / 16 →
      ‖mellinVal (δ₀ + hδ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
        (3 / 2) * ‖mellinVal (δ₀ + hδ) ((1 / 2 : ℂ) - Complex.I)‖ := by
  cases sc with
  | M v0r v0i vdr vdi vtr vti vt2r vt2i udMSum qt =>
    simp only [checkStrip, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.mul_eq, Nat.add_eq, nat_div_def] at hchk
    rw [← PAD_nat_eq] at hchk
    obtain ⟨⟨ev0r, ev0i, evdr, evdi, evtr, evti, evt2r, evt2i⟩, hokUd, hqt⟩ := hchk
    let ω := 6 * pi0R * δ₀
    have h6pi0_pos : (0 : ℝ) < 6 * pi0R := mul_pos (by norm_num) pi0R_pos
    have hω : |ω| ≤ 19 := by
      obtain ⟨_, _, _, h6⟩ := pi_approx_pi0R
      dsimp [ω]; rw [abs_mul, abs_of_pos h6pi0_pos]
      linarith [mul_le_mul_of_nonneg_left hδ₀ h6pi0_pos.le]
    let t₀ : ℝ := -(p : ℝ) / 16
    let s₀ : ℂ := (1 / 2 : ℂ) + (t₀ : ℝ) * Complex.I
    have hs₀_eq : s₀ = (1 / 2 : ℂ) + ((-(p : ℝ) / ((16 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I := by
      dsimp [s₀, t₀]
    obtain ⟨s0r, s0i, sdr, sdi, str, sti, st2r, st2i⟩ :=
      all_strip_sums_sound hω hshape hb p 16 (by norm_num)
    rw [← hs₀_eq] at s0r s0i sdr sdi str sti st2r st2i
    rw [← ev0r] at s0r; rw [← ev0i] at s0i; rw [← evdr] at sdr; rw [← evdi] at sdi
    rw [← evtr] at str; rw [← evti] at sti; rw [← evt2r] at st2r; rw [← evt2i] at st2i
    obtain ⟨hJ0_bd, hJt_bd, hJt2_bd⟩ := norm_polyJ_le hω s₀ (by simp [s₀])
    have mag_from_err : ∀ (v : ℕ) (c : ℝ), |c| ≤ 8 * 3 ^ 22 →
        |valZ Z_nat v - (S_nat : ℝ) * c| ≤ E_SUM → |valZ Z_nat v| ≤ (Z_nat : ℝ) / 4 := by
      intro v c hc herr
      have htri := abs_le_abs_add_err (valZ Z_nat v) ((S_nat : ℝ) * c)
      rw [abs_mul, abs_of_pos S_nat_pos] at htri
      have hS : (S_nat : ℝ) * |c| ≤ (S_nat : ℝ) * (8 * 3 ^ 22) :=
        mul_le_mul_of_nonneg_left hc S_nat_pos.le
      linarith [S_polyJ_le_Z_div_4]
    have hv0r_p : |valZ Z_nat v0r - (S_nat : ℝ) * (polyJ0 ω s₀).re| ≤ E_SUM ∧ |valZ Z_nat v0r| ≤ (Z_nat : ℝ) / 4 :=
      ⟨s0r, mag_from_err _ _ (le_trans (Complex.abs_re_le_norm _) hJ0_bd) s0r⟩
    have hv0i_p : |valZ Z_nat v0i - (S_nat : ℝ) * (polyJ0 ω s₀).im| ≤ E_SUM ∧ |valZ Z_nat v0i| ≤ (Z_nat : ℝ) / 4 :=
      ⟨s0i, mag_from_err _ _ (le_trans (Complex.abs_im_le_norm _) hJ0_bd) s0i⟩
    have hvtr_p : |valZ Z_nat vtr - (S_nat : ℝ) * (polyJt ω s₀).re| ≤ E_SUM ∧ |valZ Z_nat vtr| ≤ (Z_nat : ℝ) / 4 :=
      ⟨str, mag_from_err _ _ (le_trans (Complex.abs_re_le_norm _) hJt_bd) str⟩
    have hvti_p : |valZ Z_nat vti - (S_nat : ℝ) * (polyJt ω s₀).im| ≤ E_SUM ∧ |valZ Z_nat vti| ≤ (Z_nat : ℝ) / 4 :=
      ⟨sti, mag_from_err _ _ (le_trans (Complex.abs_im_le_norm _) hJt_bd) sti⟩
    have hvt2r_p : |valZ Z_nat vt2r - (S_nat : ℝ) * (polyJt2 ω s₀).re| ≤ E_SUM ∧ |valZ Z_nat vt2r| ≤ (Z_nat : ℝ) / 4 :=
      ⟨st2r, mag_from_err _ _ (le_trans (Complex.abs_re_le_norm _) hJt2_bd) st2r⟩
    have hvt2i_p : |valZ Z_nat vt2i - (S_nat : ℝ) * (polyJt2 ω s₀).im| ≤ E_SUM ∧ |valZ Z_nat vt2i| ≤ (Z_nat : ℝ) / 4 :=
      ⟨st2i, mag_from_err _ _ (le_trans (Complex.abs_im_le_norm _) hJt2_bd) st2i⟩
    have hud_sum : (S_nat : ℝ) * ‖polyJdRaw ω s₀‖ ≤ (udMSum : ℝ) := by
      have hre : |(((S_nat : ℝ) : ℂ) * polyJdRaw ω s₀).re| ≤ ((onatAbs Z_nat vdr + PAD_nat : ℕ) : ℝ) := by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Nat.cast_add, onatAbs_eq_abs]
        have := abs_le_abs_add_err ((S_nat : ℝ) * (polyJdRaw ω s₀).re) (valZ Z_nat vdr)
        rw [abs_sub_comm] at this
        linarith [E_SUM_le_PAD]
      have him : |(((S_nat : ℝ) : ℂ) * polyJdRaw ω s₀).im| ≤ ((onatAbs Z_nat vdi + PAD_nat : ℕ) : ℝ) := by
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Nat.cast_add, onatAbs_eq_abs]
        have := abs_le_abs_add_err ((S_nat : ℝ) * (polyJdRaw ω s₀).im) (valZ Z_nat vdi)
        rw [abs_sub_comm] at this
        linarith [E_SUM_le_PAD]
      have h1 : ‖((S_nat : ℝ) : ℂ) * polyJdRaw ω s₀‖ ≤ (udMSum : ℝ) := by
        refine norm_complex_le_of_re_im_sq hre him (Nat.cast_nonneg _) ?_
        rw [sq, sq, sq]; exact_mod_cast hokUd
      rwa [norm_mul, Complex.norm_real, Real.norm_of_nonneg S_nat_pos.le] at h1
    let baseReal : ℝ := (1 / 780 : ℝ) + |hδ| * ((6 * pi0R) * ‖polyJdRaw ω s₀‖ + (1 / 6000 : ℝ)) + 40 * hδ ^ 2
    let udM := W6_HI_nat * udMSum / S_nat + 1
    let baseErrD := ERR0_nat + (((udM + ERRD_nat) / shD + 1) + (40 * S_nat / (shD * shD) + 1))
    have hbase_le : baseReal ≤ (baseErrD : ℝ) / (S_nat : ℝ) := by
      rw [le_div_iff₀ S_nat_pos]
      have hudM_le : (S_nat : ℝ) * ((6 * pi0R) * ‖polyJdRaw ω s₀‖) ≤ (udM : ℝ) := by
        dsimp only [udM]
        calc
          (S_nat : ℝ) * ((6 * pi0R) * ‖polyJdRaw ω s₀‖)
            = (6 * pi0R) * ((S_nat : ℝ) * ‖polyJdRaw ω s₀‖) := by ring
          _ ≤ ((W6_HI_nat : ℝ) / (S_nat : ℝ)) * (udMSum : ℝ) :=
              mul_le_mul w6_pi0_le hud_sum (mul_nonneg S_nat_pos.le (norm_nonneg _))
                (div_nonneg (Nat.cast_nonneg _) S_nat_pos.le)
          _ = ((W6_HI_nat * udMSum : ℕ) : ℝ) / (S_nat : ℝ) := by push_cast; ring
          _ ≤ ((W6_HI_nat * udMSum / S_nat + 1 : ℕ) : ℝ) := nat_div_add_one_ge _ _ S_nat_pos_nat
      have hterm_d : (S_nat : ℝ) * (|hδ| * ((6 * pi0R) * ‖polyJdRaw ω s₀‖ + 1 / 6000)) ≤
          (((udM + ERRD_nat) / shD + 1 : ℕ) : ℝ) := by
        have hnn_inner : 0 ≤ (S_nat : ℝ) * ((6 * pi0R) * ‖polyJdRaw ω s₀‖) + (S_nat : ℝ) * (1 / 6000) :=
          add_nonneg (mul_nonneg S_nat_pos.le (mul_nonneg h6pi0_pos.le (norm_nonneg _)))
            (mul_nonneg S_nat_pos.le (by norm_num))
        calc
          (S_nat : ℝ) * (|hδ| * ((6 * pi0R) * ‖polyJdRaw ω s₀‖ + 1 / 6000))
            = |hδ| * ((S_nat : ℝ) * ((6 * pi0R) * ‖polyJdRaw ω s₀‖) + (S_nat : ℝ) * (1 / 6000)) := by ring
          _ ≤ (1 / (shD : ℝ)) * ((udM : ℝ) + (ERRD_nat : ℝ)) :=
              mul_le_mul hhδ (add_le_add hudM_le S_errD_le) hnn_inner (by positivity)
          _ = ((udM + ERRD_nat : ℕ) : ℝ) / (shD : ℝ) := by push_cast; ring
          _ ≤ (((udM + ERRD_nat) / shD + 1 : ℕ) : ℝ) := nat_div_add_one_ge _ _ hshD
      have hhδ2 : hδ ^ 2 ≤ 1 / ((shD * shD : ℕ) : ℝ) := by
        have h1 : |hδ| ^ 2 ≤ (1 / (shD : ℝ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hhδ 2
        rw [sq_abs, div_pow] at h1; simpa [sq] using h1
      have hterm_40 : (S_nat : ℝ) * (40 * hδ ^ 2) ≤ ((40 * S_nat / (shD * shD) + 1 : ℕ) : ℝ) := by
        calc
          (S_nat : ℝ) * (40 * hδ ^ 2) = (40 * (S_nat : ℝ)) * hδ ^ 2 := by ring
          _ ≤ (40 * (S_nat : ℝ)) * (1 / ((shD * shD : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left hhδ2 (mul_nonneg (by norm_num) S_nat_pos.le)
          _ = ((40 * S_nat : ℕ) : ℝ) / ((shD * shD : ℕ) : ℝ) := by push_cast; ring
          _ ≤ ((40 * S_nat / (shD * shD) + 1 : ℕ) : ℝ) := nat_div_add_one_ge _ _ (Nat.mul_pos hshD hshD)
      dsimp only [baseReal, baseErrD]
      rw [Nat.cast_add, Nat.cast_add]
      linarith only [S_err0_le, hterm_d, hterm_40]
    intro t ht_lo ht_hi
    let ht : ℝ := t - t₀
    have hht_16 : |ht - signB false * ((0 : ℕ) : ℝ) / ((2 ^ 4 : ℕ) : ℝ)| ≤ 1 / ((2 ^ 4 : ℕ) : ℝ) := by
      dsimp [ht, t₀, signB]; norm_num
      rw [abs_le]; constructor <;> linarith
    have hq_res := checkQTree_sound hshD hhδ hbase_le hden
      hv0r_p hv0i_p hvtr_p hvti_p hvt2r_p hvt2i_p qt false 0 4 hqt ht hht_16
    have ht_eq : t = t₀ + ht := by dsimp [ht]; ring
    rw [ht_eq]
    have hnum_jet := mellin_num_jet_le hδ₀ hδ t₀ ht
    dsimp only [ω, s₀] at hnum_jet hq_res
    have hsq3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    calc
      ‖mellinVal (δ₀ + hδ) ((1 / 2 : ℂ) + ((t₀ + ht : ℝ) : ℂ) * Complex.I)‖
        ≤ Real.sqrt 3 * (baseReal + ‖polyJ0 ω s₀ + (ht : ℂ) * polyJt ω s₀ + ((ht ^ 2 : ℝ) : ℂ) * polyJt2 ω s₀‖ +
            |ht| * (1 / 20000) + ht ^ 2 * (1 / 10000) + 10 * |ht| * |hδ| + 16 * |ht| ^ 3) := by
          dsimp [baseReal]; linarith [hnum_jet]
      _ ≤ Real.sqrt 3 * ((3 / 2) * denReal) :=
          mul_le_mul_of_nonneg_left (by linarith [hq_res]) hsq3_pos.le
      _ = (3 / 2) * (Real.sqrt 3 * denReal) := by ring
      _ ≤ (3 / 2) * ‖mellinVal (δ₀ + hδ) ((1 / 2 : ℂ) - Complex.I)‖ :=
          mul_le_mul_of_nonneg_left hden_val (by norm_num)

private lemma ite_false_eq_true {c : Prop} [Decidable c] {b : Bool}
    (h : (if c then b else false) = true) : c ∧ b = true := by
  by_cases hc : c
  · rw [if_pos hc] at h; exact ⟨hc, h⟩
  · rw [if_neg hc] at h; exact absurd h Bool.false_ne_true

lemma checkFastDTree_sound (dNeg : Bool) (dt : FastDTree) (kAbs qD : ℕ)
    (hk_inv : kAbs < 2 ^ qD)
    (hchk : checkFastDTree S_nat Z_nat PI0_DEN_nat W6_NUM_nat W6_HI_nat
      ERR0_nat ERRD_nat ERRT_nat ERRT2_nat dNeg dt kAbs qD = true) :
    let δMid := signB dNeg * ((2 * kAbs + 1 : ℕ) : ℝ) / ((2 ^ (qD + 1) : ℕ) : ℝ)
    let δRad := 1 / ((2 ^ (qD + 1) : ℕ) : ℝ)
    ∀ δ t : ℝ, |δ - δMid| ≤ δRad → -(23 / 16) ≤ t → t ≤ -1 →
      ‖mellinVal δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
        (3 / 2) * ‖mellinVal δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  induction dt generalizing kAbs qD with
  | dsplit l r ihl ihr =>
    simp only [checkFastDTree, Bool.and_eq_true, Nat.add_eq, Nat.mul_eq] at hchk
    obtain ⟨hkl, hkr⟩ := hchk
    intro δMid δRad δ t hδ ht_lo ht_hi
    have hk_l : 2 * kAbs < 2 ^ (qD + 1) := by rw [pow_succ]; omega
    have hk_r : 2 * kAbs + 1 < 2 ^ (qD + 1) := by rw [pow_succ]; omega
    have hpow2 : ((2 ^ (qD + 1 + 1) : ℕ) : ℝ) = 2 * ((2 ^ (qD + 1) : ℕ) : ℝ) := by
      rw [pow_succ, Nat.cast_mul, Nat.cast_ofNat]; ring
    have hpos : (0 : ℝ) < ((2 ^ (qD + 1) : ℕ) : ℝ) := by positivity
    cases dNeg
    · dsimp [δMid, δRad, signB] at hδ
      rcases le_total δ (((2 * kAbs + 1 : ℕ) : ℝ) / ((2 ^ (qD + 1) : ℕ) : ℝ)) with hside | hside
      · apply ihl (2 * kAbs) (qD + 1) hk_l hkl δ t _ ht_lo ht_hi
        simp only [signB, Bool.false_eq_true, ↓reduceIte, one_mul, hpow2, abs_le]
        have hlo := (abs_le.mp hδ).1
        push_cast at hlo hside ⊢
        constructor <;> { field_simp [hpos.ne'] at hlo hside ⊢; nlinarith only [hlo, hside, hpos] }
      · apply ihr (2 * kAbs + 1) (qD + 1) hk_r hkr δ t _ ht_lo ht_hi
        simp only [signB, Bool.false_eq_true, ↓reduceIte, one_mul, hpow2, abs_le]
        have hhi := (abs_le.mp hδ).2
        push_cast at hhi hside ⊢
        constructor <;> { field_simp [hpos.ne'] at hhi hside ⊢; nlinarith only [hhi, hside, hpos] }
    · dsimp [δMid, δRad, signB] at hδ
      rcases le_total (-(((2 * kAbs + 1 : ℕ) : ℝ) / ((2 ^ (qD + 1) : ℕ) : ℝ))) δ with hside | hside
      · apply ihl (2 * kAbs) (qD + 1) hk_l hkl δ t _ ht_lo ht_hi
        simp only [signB, ↓reduceIte, neg_one_mul, hpow2, abs_le]
        have hhi := (abs_le.mp hδ).2
        push_cast at hhi hside ⊢
        constructor <;> { field_simp [hpos.ne'] at hhi hside ⊢; nlinarith only [hhi, hside, hpos] }
      · apply ihr (2 * kAbs + 1) (qD + 1) hk_r hkr δ t _ ht_lo ht_hi
        simp only [signB, ↓reduceIte, neg_one_mul, hpow2, abs_le]
        have hlo := (abs_le.mp hδ).1
        push_cast at hlo hside ⊢
        constructor <;> { field_simp [hpos.ne'] at hlo hside ⊢; nlinarith only [hlo, hside, hpos] }
  | dleaf bt dv0r dv0i dvdr dvdi lDen udDenSum s17 s19 s21 s23 =>
    unfold checkFastDTree at hchk
    rw [← PAD_nat_eq] at hchk
    simp only [Nat.add_eq, Nat.mul_eq, Nat.pow_eq, Nat.sub_eq, nat_div_def] at hchk
    obtain ⟨hB_and_den, hchk⟩ := ite_false_eq_true hchk
    obtain ⟨hDen_checks, hchk⟩ := ite_false_eq_true hchk
    simp only [Bool.and_eq_true, Nat.beq_eq] at hB_and_den
    obtain ⟨hBTree, edv0r, edv0i, edvdr, edvdi⟩ := hB_and_den
    simp only [Bool.and_eq_true, Nat.ble_eq] at hDen_checks
    obtain ⟨hokL, hokUd, hsub_lt_l⟩ := hDen_checks
    simp only [Bool.and_eq_true] at hchk
    obtain ⟨hs17, hs19, hs21, hs23⟩ := hchk
    intro δMid δRad δ t hδ_rad ht_lo ht_hi
    set dNum := 2 * kAbs + 1
    set dq1 := qD + 1
    set shD := 2 ^ dq1
    have hshD_pos : 0 < shD := Nat.pos_of_ne_zero (pow_ne_zero dq1 (by norm_num))
    have hshDR_pos : (0 : ℝ) < (shD : ℝ) := Nat.cast_pos.mpr hshD_pos
    have hdNum_le : dNum ≤ shD := by dsimp [dNum, shD, dq1]; rw [pow_succ]; omega
    have hδMid_abs : |δMid| ≤ 1 := by
      dsimp [δMid]
      rw [abs_div, abs_mul, abs_signB, one_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos hshDR_pos]
      exact (div_le_one hshDR_pos).mpr (Nat.cast_le.mpr hdNum_le)
    let denBase := PI0_DEN_nat * shD
    let numW := W6_NUM_nat * dNum
    have hdenBase_pos : 0 < denBase := Nat.mul_pos PI0_DEN_nat_pos hshD_pos
    have hPI0R_ne : (PI0_DEN_nat : ℝ) ≠ 0 := (Nat.cast_pos.mpr PI0_DEN_nat_pos).ne'
    have hω_eq : signB dNeg * (numW : ℝ) / (denBase : ℝ) = 6 * pi0R * δMid := by
      dsimp only [numW, denBase, δMid, shD, dq1, dNum]
      push_cast; rw [w6_num_eq_pi0]; field_simp [hPI0R_ne, hshDR_pos.ne']
    have h6pi0_pos : (0 : ℝ) < 6 * pi0R := mul_pos (by norm_num) pi0R_pos
    have hω_le19 : |signB dNeg * (numW : ℝ) / (denBase : ℝ)| ≤ 19 := by
      rw [hω_eq]
      obtain ⟨_, _, _, h6⟩ := pi_approx_pi0R
      rw [abs_mul, abs_of_pos h6pi0_pos]; linarith [mul_le_mul_of_nonneg_left hδMid_abs h6pi0_pos.le]
    obtain ⟨hshape, hb⟩ := checkBTree_sound hdenBase_pos hω_le19 hBTree
    rw [hω_eq] at hb
    let ω := 6 * pi0R * δMid
    have hω : |ω| ≤ 19 := by dsimp [ω]; rwa [← hω_eq]
    obtain ⟨sd0r, sd0i, sddr, sddi, _, _, _, _⟩ := all_strip_sums_sound hω hshape hb 1 1 (by norm_num)
    have hsm1_eq : ((1 / 2 : ℂ) + ((-((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) = (1 / 2 : ℂ) - Complex.I := by
      norm_num; ring
    rw [hsm1_eq] at sd0r sd0i sddr sddi
    rw [← edv0r] at sd0r; rw [← edv0i] at sd0i; rw [← edvdr] at sddr; rw [← edvdi] at sddi
    let sm1 : ℂ := (1 / 2 : ℂ) - Complex.I
    have hlDen_le : (lDen : ℝ) ≤ (S_nat : ℝ) * ‖polyJ0 ω sm1‖ := by
      let rLo := onatAbs Z_nat dv0r - PAD_nat
      let iLo := onatAbs Z_nat dv0i - PAD_nat
      have hr_ge : (rLo : ℝ) ≤ |(((S_nat : ℝ) : ℂ) * polyJ0 ω sm1).re| := by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        by_cases hge : PAD_nat ≤ onatAbs Z_nat dv0r
        · dsimp [rLo]; rw [Nat.cast_sub hge, onatAbs_eq_abs]
          have := abs_ge_abs_sub_err ((S_nat : ℝ) * (polyJ0 ω sm1).re) (valZ Z_nat dv0r)
          linarith [E_SUM_le_PAD]
        · have h0 : rLo = 0 := Nat.sub_eq_zero_of_le (le_of_not_ge hge)
          rw [h0, Nat.cast_zero]; exact abs_nonneg _
      have hi_ge : (iLo : ℝ) ≤ |(((S_nat : ℝ) : ℂ) * polyJ0 ω sm1).im| := by
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
        by_cases hge : PAD_nat ≤ onatAbs Z_nat dv0i
        · dsimp [iLo]; rw [Nat.cast_sub hge, onatAbs_eq_abs]
          have := abs_ge_abs_sub_err ((S_nat : ℝ) * (polyJ0 ω sm1).im) (valZ Z_nat dv0i)
          linarith [E_SUM_le_PAD]
        · have h0 : iLo = 0 := Nat.sub_eq_zero_of_le (le_of_not_ge hge)
          rw [h0, Nat.cast_zero]; exact abs_nonneg _
      have h1 : (lDen : ℝ) ≤ ‖((S_nat : ℝ) : ℂ) * polyJ0 ω sm1‖ := by
        refine norm_complex_ge_of_re_im_sq (Nat.cast_nonneg _) (Nat.cast_nonneg _) hr_ge hi_ge
          (Nat.cast_nonneg _) ?_
        have hsq : ((lDen * lDen : ℕ) : ℝ) ≤ ((rLo * rLo + iLo * iLo : ℕ) : ℝ) := by exact_mod_cast hokL
        push_cast at hsq; simpa [sq] using hsq
      rwa [norm_mul, Complex.norm_real, Real.norm_of_nonneg S_nat_pos.le] at h1
    have hudDen_sum : (S_nat : ℝ) * ‖polyJdRaw ω sm1‖ ≤ (udDenSum : ℝ) := by
      have hre : |(((S_nat : ℝ) : ℂ) * polyJdRaw ω sm1).re| ≤ ((onatAbs Z_nat dvdr + PAD_nat : ℕ) : ℝ) := by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Nat.cast_add, onatAbs_eq_abs]
        have := abs_le_abs_add_err ((S_nat : ℝ) * (polyJdRaw ω sm1).re) (valZ Z_nat dvdr)
        rw [abs_sub_comm] at this
        linarith [E_SUM_le_PAD]
      have him : |(((S_nat : ℝ) : ℂ) * polyJdRaw ω sm1).im| ≤ ((onatAbs Z_nat dvdi + PAD_nat : ℕ) : ℝ) := by
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Nat.cast_add, onatAbs_eq_abs]
        have := abs_le_abs_add_err ((S_nat : ℝ) * (polyJdRaw ω sm1).im) (valZ Z_nat dvdi)
        rw [abs_sub_comm] at this
        linarith [E_SUM_le_PAD]
      have h1 : ‖((S_nat : ℝ) : ℂ) * polyJdRaw ω sm1‖ ≤ (udDenSum : ℝ) := by
        refine norm_complex_le_of_re_im_sq hre him (Nat.cast_nonneg _) ?_
        rw [sq, sq, sq]; exact_mod_cast hokUd
      rwa [norm_mul, Complex.norm_real, Real.norm_of_nonneg S_nat_pos.le] at h1
    let hδ := δ - δMid
    have hhδ : |hδ| ≤ 1 / (shD : ℝ) := hδ_rad
    let udDen := W6_HI_nat * udDenSum / S_nat + 1
    let subDen := ((udDen + ERRD_nat) / shD + 1) + (ERR0_nat + (40 * S_nat / (shD * shD) + 1))
    let denLo := lDen - subDen
    let denReal : ℝ := ‖polyJ0 ω sm1‖ - ((1 / 780 : ℝ) + |hδ| * ((6 * pi0R) * ‖polyJdRaw ω sm1‖ + (1 / 6000 : ℝ)) + 40 * hδ ^ 2)
    have hsub_le : (S_nat : ℝ) * ((1 / 780 : ℝ) + |hδ| * ((6 * pi0R) * ‖polyJdRaw ω sm1‖ + (1 / 6000 : ℝ)) + 40 * hδ ^ 2) ≤ (subDen : ℝ) := by
      have hudDen_le : (S_nat : ℝ) * ((6 * pi0R) * ‖polyJdRaw ω sm1‖) ≤ (udDen : ℝ) := by
        dsimp only [udDen]
        calc
          (S_nat : ℝ) * ((6 * pi0R) * ‖polyJdRaw ω sm1‖)
            = (6 * pi0R) * ((S_nat : ℝ) * ‖polyJdRaw ω sm1‖) := by ring
          _ ≤ ((W6_HI_nat : ℝ) / (S_nat : ℝ)) * (udDenSum : ℝ) :=
              mul_le_mul w6_pi0_le hudDen_sum (mul_nonneg S_nat_pos.le (norm_nonneg _))
                (div_nonneg (Nat.cast_nonneg _) S_nat_pos.le)
          _ = ((W6_HI_nat * udDenSum : ℕ) : ℝ) / (S_nat : ℝ) := by push_cast; ring
          _ ≤ ((W6_HI_nat * udDenSum / S_nat + 1 : ℕ) : ℝ) := nat_div_add_one_ge _ _ S_nat_pos_nat
      have hterm_d : (S_nat : ℝ) * (|hδ| * ((6 * pi0R) * ‖polyJdRaw ω sm1‖ + 1 / 6000)) ≤
          (((udDen + ERRD_nat) / shD + 1 : ℕ) : ℝ) := by
        have hnn_inner : 0 ≤ (S_nat : ℝ) * ((6 * pi0R) * ‖polyJdRaw ω sm1‖) + (S_nat : ℝ) * (1 / 6000) :=
          add_nonneg (mul_nonneg S_nat_pos.le (mul_nonneg h6pi0_pos.le (norm_nonneg _)))
            (mul_nonneg S_nat_pos.le (by norm_num))
        calc
          (S_nat : ℝ) * (|hδ| * ((6 * pi0R) * ‖polyJdRaw ω sm1‖ + 1 / 6000))
            = |hδ| * ((S_nat : ℝ) * ((6 * pi0R) * ‖polyJdRaw ω sm1‖) + (S_nat : ℝ) * (1 / 6000)) := by ring
          _ ≤ (1 / (shD : ℝ)) * ((udDen : ℝ) + (ERRD_nat : ℝ)) :=
              mul_le_mul hhδ (add_le_add hudDen_le S_errD_le) hnn_inner (by positivity)
          _ = ((udDen + ERRD_nat : ℕ) : ℝ) / (shD : ℝ) := by push_cast; ring
          _ ≤ (((udDen + ERRD_nat) / shD + 1 : ℕ) : ℝ) := nat_div_add_one_ge _ _ hshD_pos
      have hhδ2 : hδ ^ 2 ≤ 1 / ((shD * shD : ℕ) : ℝ) := by
        have h1 : |hδ| ^ 2 ≤ (1 / (shD : ℝ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hhδ 2
        rw [sq_abs, div_pow] at h1; simpa [sq] using h1
      have hterm_40 : (S_nat : ℝ) * (40 * hδ ^ 2) ≤ ((40 * S_nat / (shD * shD) + 1 : ℕ) : ℝ) := by
        calc
          (S_nat : ℝ) * (40 * hδ ^ 2) = (40 * (S_nat : ℝ)) * hδ ^ 2 := by ring
          _ ≤ (40 * (S_nat : ℝ)) * (1 / ((shD * shD : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left hhδ2 (mul_nonneg (by norm_num) S_nat_pos.le)
          _ = ((40 * S_nat : ℕ) : ℝ) / ((shD * shD : ℕ) : ℝ) := by push_cast; ring
          _ ≤ ((40 * S_nat / (shD * shD) + 1 : ℕ) : ℝ) := nat_div_add_one_ge _ _ (Nat.mul_pos hshD_pos hshD_pos)
      have hsub_cast : (subDen : ℝ) =
          (((udDen + ERRD_nat) / shD + 1 : ℕ) : ℝ) + ((ERR0_nat : ℝ) + ((40 * S_nat / (shD * shD) + 1 : ℕ) : ℝ)) := by
        dsimp only [subDen]; push_cast; ring
      rw [hsub_cast]
      linarith only [S_err0_le, hterm_d, hterm_40]
    have hden_le : (denLo : ℝ) / (S_nat : ℝ) ≤ denReal := by
      rw [div_le_iff₀ S_nat_pos]
      have hsub_le_l : subDen ≤ lDen := Nat.le_of_lt hsub_lt_l
      dsimp [denLo, denReal]; rw [Nat.cast_sub hsub_le_l]
      linarith only [hlDen_le, hsub_le]
    have hδ_eq : δ = δMid + hδ := by dsimp [hδ]; ring
    rw [hδ_eq]
    have hden_val : Real.sqrt 3 * denReal ≤ ‖mellinVal (δMid + hδ) ((1 / 2 : ℂ) - Complex.I)‖ :=
      mellin_den_jet_ge hδMid_abs hδ
    by_cases ht17 : -(18 / 16 : ℝ) ≤ t
    · exact checkStrip_sound hδMid_abs hshD_pos hhδ hden_le hden_val hshape hb hs17 t
        (by norm_num; linarith) (by norm_num; linarith)
    · by_cases ht19 : -(20 / 16 : ℝ) ≤ t
      · exact checkStrip_sound hδMid_abs hshD_pos hhδ hden_le hden_val hshape hb hs19 t
          (by norm_num; linarith) (by norm_num; linarith)
      · by_cases ht21 : -(22 / 16 : ℝ) ≤ t
        · exact checkStrip_sound hδMid_abs hshD_pos hhδ hden_le hden_val hshape hb hs21 t
            (by norm_num; linarith) (by norm_num; linarith)
        · exact checkStrip_sound hδMid_abs hshD_pos hhδ hden_le hden_val hshape hb hs23 t
            (by norm_num; linarith) (by norm_num; linarith)

theorem sound_all_fast (dtNeg dtPos : FastDTree)
    (hNeg : checkFastDTree S_nat Z_nat PI0_DEN_nat W6_NUM_nat W6_HI_nat
      ERR0_nat ERRD_nat ERRT_nat ERRT2_nat true dtNeg 0 0 = true)
    (hPos : checkFastDTree S_nat Z_nat PI0_DEN_nat W6_NUM_nat W6_HI_nat
      ERR0_nat ERRD_nat ERRT_nat ERRT2_nat false dtPos 0 0 = true)
    (δ : ℝ) (hδ : |δ| ≤ 1) {t : ℝ} (hlo : -(23 / 16) ≤ t) (hhi : t ≤ -1) :
    ‖mellinVal δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖mellinVal δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  have hd_bounds := abs_le.mp hδ
  rcases le_total δ 0 with hneg_d | hpos_d
  · apply checkFastDTree_sound true dtNeg 0 0 (by norm_num) hNeg δ t _ hlo hhi
    simp [signB]; rw [abs_le]; constructor <;> linarith
  · apply checkFastDTree_sound false dtPos 0 0 (by norm_num) hPos δ t _ hlo hhi
    simp [signB]; rw [abs_le]; constructor <;> linarith

theorem sound_all_fast_lit (dtNeg dtPos : FastDTree)
    (hNeg : checkFastDTree 1208925819614629174706176 1329227995784915872903807060280344576
      100000000000 1884955592154 22787714841819531240894044
      1549904896941832275265 201487636602438195785 60446290980731458736 120892581961462917471
      true dtNeg 0 0 = true)
    (hPos : checkFastDTree 1208925819614629174706176 1329227995784915872903807060280344576
      100000000000 1884955592154 22787714841819531240894044
      1549904896941832275265 201487636602438195785 60446290980731458736 120892581961462917471
      false dtPos 0 0 = true)
    (δ : ℝ) (hδ : |δ| ≤ 1) {t : ℝ} (hlo : -(23 / 16) ≤ t) (hhi : t ≤ -1) :
    ‖mellinVal δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖mellinVal δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  rw [← S_nat_eq, ← Z_nat_eq, ← PI0_DEN_nat_eq, ← W6_NUM_nat_eq, ← W6_HI_nat_eq,
    ← ERR0_nat_eq, ← ERRD_nat_eq, ← ERRT_nat_eq, ← ERRT2_nat_eq] at hNeg hPos
  exact sound_all_fast dtNeg dtPos hNeg hPos δ hδ hlo hhi


theorem sound_subtree_lit (dNeg : Bool) (dt : FastDTree) (kAbs qD : ℕ)
    (hk_inv : kAbs < 2 ^ qD)
    (hOk : checkFastDTree 1208925819614629174706176 1329227995784915872903807060280344576
      100000000000 1884955592154 22787714841819531240894044
      1549904896941832275265 201487636602438195785 60446290980731458736 120892581961462917471
      dNeg dt kAbs qD = true)
    (δ : ℝ)
    (hδ_box : |δ - signB dNeg * ((2 * kAbs + 1 : ℕ) : ℝ) / ((2 ^ (qD + 1) : ℕ) : ℝ)| ≤
      1 / ((2 ^ (qD + 1) : ℕ) : ℝ))
    {t : ℝ} (hlo : -(23 / 16) ≤ t) (hhi : t ≤ -1) :
    ‖mellinVal δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖mellinVal δ ((1 / 2 : ℂ) - Complex.I)‖ := by
  rw [← S_nat_eq, ← Z_nat_eq, ← PI0_DEN_nat_eq, ← W6_NUM_nat_eq, ← W6_HI_nat_eq,
    ← ERR0_nat_eq, ← ERRD_nat_eq, ← ERRT_nat_eq, ← ERRT2_nat_eq] at hOk
  exact checkFastDTree_sound dNeg dt kAbs qD hk_inv hOk δ t hδ_box hlo hhi

end
end GaussSmallBridge

namespace GaussSmallBridge
open BTree QTree StripCert FastDTree

private def zL : BTree := L 0x1000000000000000000000000000000

private theorem checkFastDTree_dsplit (s z pi0Den w6Num w6Hi err0I errDI errTI errT2I : Nat)
  (dNeg : Bool) (l r : FastDTree) (kAbs qD kL kR qD1 : Nat)
  (hkL : Nat.mul 2 kAbs = kL) (hkR : Nat.add (Nat.mul 2 kAbs) 1 = kR) (hq : Nat.add qD 1 = qD1)
  (hl : checkFastDTree s z pi0Den w6Num w6Hi err0I errDI errTI errT2I dNeg l kL qD1 = true)
  (hr : checkFastDTree s z pi0Den w6Num w6Hi err0I errDI errTI errT2I dNeg r kR qD1 = true) :
  checkFastDTree s z pi0Den w6Num w6Hi err0I errDI errTI errT2I dNeg (dsplit l r) kAbs qD = true := by
  subst hkL; subst hkR; subst hq
  simp only [checkFastDTree, hl, hr, Bool.and_self]

private def cneg_bt_0 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xffffffffffb49a0e033373426a7a47) (L 0x100000000048b1a72317b08e873c4e7))) (N (L 0xfffffffffeab9e30984488e4ed7a65) (N (L 0x1000000000a520b8df5efeabadb3310) (L 0xfffffffffcffaed6f47e15ba332f92)))) (N (N (L 0x1000000000fa0c849d35a36f60c8268) (N (L 0xfffffffffb7bd4cf734bf0718d23d7) (L 0x10000000011bf71f5327d67113b2587))) (N (L 0xfffffffffae725bbb90662c0acd57c) (N (L 0x100000000101f881e6e9d8ca5dcc21e) (L 0xfffffffffb65e100ef3fe9b26670a4))))) (N (N (N (L 0x1000000000c34907134e326885b9c8c) (N (L 0xfffffffffc8996a63595f518a5994a) (L 0x10000000007eb4bd866cd2080b6b3a4))) (N (L 0xfffffffffdc458e3150750a472bf6a) (N (L 0x100000000047ee0836614931209f051) (L 0xfffffffffebd6be0662821e988d073)))) (N (N (L 0x1000000000244b77882f55b3b75db98) (N (L 0xffffffffff5e32a01a8b1554f394b3) (L 0x1000000000107b48abbca4926444375))) (N (L 0xffffffffffb6f52d5ef0f843a61c37) (N (L 0x100000000006cdb75effcac77a5033c) (L 0xffffffffffe2063719a1c8260042f8)))))) (N (N (N (N (L 0x1000000000029307821e41ad440a7ca) (N (L 0xfffffffffff4b936a03e0b7b6a7e40) (L 0x100000000000e62b5af02ea723ac8e4))) (N (L 0xfffffffffffc1590cf4cc53c0cc21b) (N (L 0x1000000000004aa45bf475738c97a31) (L 0xfffffffffffebcc548f94ba2b7968d)))) (N (N (L 0x100000000000169747cf605feb7cd22) (N (L 0xffffffffffff9eb9a104583802857f) (L 0x1000000000000668df5f985be79b215))) (N (L 0xffffffffffffe48e20d28bf13624fb) (N (L 0x10000000000001b627078a86f1466f8) (L 0xfffffffffffff8b65ac37fe1c644eb))))) (N (N (N (L 0x100000000000006e7df843b7a2daa72) (N (L 0xfffffffffffffe2c1f33110ee8b176) (L 0x100000000000001a65548f32062217f))) (N (L 0xffffffffffffff90d6b557b8f0d7ce) (N (L 0x1000000000000005fd7ec583d0903b3) (L 0xffffffffffffffe6e905ed9f266019)))) (N (N (L 0x10000000000000014b6bd257773f7de) (N (L 0xfffffffffffffffa9b55ddd959bd5b) (L 0x1000000000000000445e4971f885fdf))) (N (L 0xfffffffffffffffee4b5235bf3f43c) (N (L 0x10000000000000000d7d61c2759c4e9) (L 0xffffffffffffffffc866651de61089))))))) (N (N (N (N (N (L 0x1000000000000000028cf7b5f9010de) (N (L 0xfffffffffffffffff58ade21cfe435) (L 0x10000000000000000076850fcd2848c))) (N (L 0xfffffffffffffffffe1c9d1a9f773d) (N (L 0x10000000000000000014af24b9b4e2f) (L 0xffffffffffffffffffac1391ae0974)))) (N (N (L 0x1000000000000000000379d8fdbebca) (N (L 0xfffffffffffffffffff1f81fb6a26d) (L 0x1000000000000000000090312116b9d))) (N (L 0xfffffffffffffffffffdbcf0d95cec) (N (L 0x10000000000000000000168ef2629ae) (L 0xffffffffffffffffffffa5ddff54dc))))) (N (N (N (L 0x100000000000000000000369522f8a4) (N (L 0xfffffffffffffffffffff2702c446d) (L 0x10000000000000000000007fcd9e05a))) (N (L 0xfffffffffffffffffffffe06770d46) (N (L 0x1000000000000000000000121e2354c) (L 0xffffffffffffffffffffffb8b07923)))) (N (N (L 0x1000000000000000000000027d909f7) (N (L 0xfffffffffffffffffffffff63eec27) (L 0x100000000000000000000000550f3f3))) (N (L 0xfffffffffffffffffffffffeb47c2d) (N (L 0x1000000000000000000000000b05fdf) (L 0xffffffffffffffffffffffffd53ed0)))))) (N (N (N (N (L 0x10000000000000000000000001638c0) (N (L 0xfffffffffffffffffffffffffaa3a5) (L 0x100000000000000000000000002b956))) (N (L 0xffffffffffffffffffffffffff5895) (N (L 0x100000000000000000000000000533a) (L 0xffffffffffffffffffffffffffec1e)))) (N (N (L 0x10000000000000000000000000009ad) (N (L 0xfffffffffffffffffffffffffffdb4) (L 0x1000000000000000000000000000118))) (N (L 0xffffffffffffffffffffffffffffbe) (N (L 0x100000000000000000000000000001e) (L 0xfffffffffffffffffffffffffffff9))))) (N (N (N (L 0x1000000000000000000000000000003) (N (zL) (zL))) (N (zL) (N (zL) (zL)))) (N (N (zL) (N (zL) (zL))) (N (zL) (N (zL) (zL)))))))

private def cneg_lf_0 : FastDTree := dleaf cneg_bt_0 0xffffffffffdc77737448a5a18216bc 0x100000000006e7171a21968185e1f40 0x100000000001091d9b916a917ca879f 0x1000000000020da910b57b0404fb827 0x7404c0e6b24637569d9c 0x24cbb5f2f42b57144c5e (M 0xffffffffffd79ad384ae51903b4e35 0x1000000000064712f757b36ce465d4f 0x100000000000df0105ed57f3a7c4500 0x1000000000020c22d6412269780812e 0x10000000000439d96bee8d7da2bd113 0x100000000009b64cca59b89f0eeaa91 0x10000000000995c47ada0c33c7c46ad 0x100000000004b773e34031d925eea25 0x2399acd24192c34babf4 (Q 0x6c42c237cc528cbacb40 0xa977916d3a71dd669507 0xaaec2ccb83c684f8e32b)) (M 0xffffffffffd14a00cc6f5ce96f44b3 0x1000000000052385e693e0089bd016b 0x10000000000091462a2ca171b664584 0x100000000001ff760080312e7afdd24 0x100000000002359abef616b978c97f0 0x100000000008812c8fa1c5d9e773466 0x100000000006b547969766520a41c8d 0x100000000004d993a838435da32e511 0x213b1491331dabde946c (Q 0x5e9001af6c87ee3c10d4 0x8c971839c89c6a12f0b6 0x8471842d4461595b055d)) (M 0xffffffffffce5c820c311f2aed5ea5 0x10000000000426853bec8438da74ea8 0x1000000000004d32af748bcd7316a5c 0x100000000001e8a33f8e50a6bfa3e10 0x100000000000cdce057d03d0d684d97 0x100000000007519e9cf331d855d0e0e 0x100000000004a652a33a256ebf2202e 0x10000000000498726ccc29ab2d66042 0x1eeb2c28d476c04207ba (Q 0x52e8c92c2101cbf872db 0x75ce38f80c5d0e5f7dde 0x689967a7236d095e4348)) (M 0xffffffffffcdc84fe2fcca043cddc9 0x1000000000034e2dc5248467a6803d7 0x100000000000133b77decde0c577a5f 0x100000000001caa25ecce2d9b68463d 0xfffffffffffd6245b8829be99b5c29 0x10000000000638495454aad2c47ee32 0x1000000000032b96f42457c6a359f96 0x1000000000042e56f17bc7ddf582059 0x1cb09923b258c6e971ff (Q 0x48ee0430bbf459507aa2 0x638d62ad8848ffbfe9b8 0x53f3e82585e7da073cfe))

private def cneg_bt_2 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xffffffffff1dce2a099a59c73f6ed4) (L 0x10000000004e3ee03bd53502c11ec25))) (N (L 0xfffffffffbe8b136b585d0202052a5) (N (L 0x1000000000be82f643131feecd5f3bd) (L 0xfffffffff6882ff03e2a1ae179fb67)))) (N (N (L 0x100000000134136acb5fbb9ce2b637f) (N (L 0xfffffffff1657b1610b57ce3020026) (L 0x100000000174645a61f57dd80cd8a30))) (N (L 0xffffffffef1c87604db0344ccb8c9f) (N (L 0x1000000001670747f91ac2f8748cf44) (L 0xfffffffff06131349ac089d4a3a37a))))) (N (N (N (L 0x10000000011fac71ff3da517ec81f31) (N (L 0xfffffffff3f6c1c58cf7af1365579d) (L 0x1000000000c5164a2868f9466065983))) (N (L 0xfffffffff80d8103e8bb3d85dbbb72) (N (L 0x100000000075e229dfffacfa24ab3ad) (L 0xfffffffffb68e1d8dcb74cc79887ae)))) (N (N (L 0x10000000003e8c046316bdaa688d92f) (N (L 0xfffffffffda4d395152af92a1b74bc) (L 0x10000000001dcfc4149a7578c470e98))) (N (L 0xfffffffffee96d8e88188ffeeb1e8d) (N (L 0x10000000000ce5189644abb351919a9) (L 0xffffffffff8b114c692824c5f6fa4c)))))) (N (N (N (N (L 0x1000000000051aca36fe36d499754b7) (N (L 0xffffffffffd30489011582fc80367a) (L 0x100000000001dccf1383e63fd03b4fd))) (N (L 0xfffffffffff007daec9528a9626a53) (N (L 0x100000000000a152a8e302656df75dc) (L 0xfffffffffffabc9f51d622ec8d1861)))) (N (N (L 0x10000000000032e088e0932806af3dc) (N (L 0xfffffffffffe619fbcbf130b1fd657) (L 0x1000000000000f06375239f20ffcd95))) (N (L 0xffffffffffff888d4ddbf5bee0fe2c) (N (L 0x100000000000042bc84b6ff4b19c683) (L 0xffffffffffffdf999bef3ee46f84bf))))) (N (N (N (L 0x1000000000000117ab45fa5a9853645) (N (L 0xfffffffffffff7b396840248f84df6) (L 0x1000000000000045531f2d7d8ae6bb2))) (N (L 0xfffffffffffffdfc9f17bee1b57f87) (N (L 0x10000000000000104f40912b4b563c2) (L 0xffffffffffffff893e9356b809fe84)))) (N (N (L 0x1000000000000003a6ab80b5a6606f6) (N (L 0xffffffffffffffe5f19e5542af9c37) (L 0x1000000000000000c78de7b0f67b418))) (N (L 0xfffffffffffffffa8b3b5b30a3e3b7) (N (L 0x100000000000000028b8563433e8b57) (L 0xfffffffffffffffee849192632d6e8))))))) (N (N (N (N (N (L 0x100000000000000007f4f222fc0588c) (N (L 0xffffffffffffffffca54067b5c8ad5) (L 0x1000000000000000017dd359d58e649))) (N (L 0xfffffffffffffffff61d74ef87d5fc) (N (L 0x10000000000000000044c5c93502f88) (L 0xfffffffffffffffffe3ff0d6dfccee)))) (N (N (L 0x1000000000000000000beb996b1d48c) (N (L 0xffffffffffffffffffb39e02b9bbf8) (L 0x10000000000000000001fdb7e8204b4))) (N (L 0xfffffffffffffffffff3721b7eb09e) (N (L 0x1000000000000000000052277dc780f) (L 0xfffffffffffffffffffe020f5a08be))))) (N (N (N (L 0x100000000000000000000ccae020002) (N (L 0xffffffffffffffffffffb1cc56e353) (L 0x1000000000000000000001ed37754d2))) (N (L 0xfffffffffffffffffffff4655ef575) (N (L 0x100000000000000000000047ebfd9c8) (L 0xfffffffffffffffffffffe550a1c88)))) (N (N (L 0x10000000000000000000000a2a2e440) (N (L 0xffffffffffffffffffffffc4809715) (L 0x10000000000000000000000164c69bb))) (N (L 0xfffffffffffffffffffffff7f43223) (N (L 0x1000000000000000000000002f7f04a) (L 0xfffffffffffffffffffffffef170dd)))))) (N (N (N (N (L 0x1000000000000000000000000625005) (N (L 0xffffffffffffffffffffffffdd7416) (L 0x10000000000000000000000000c5e92))) (N (L 0xfffffffffffffffffffffffffbb56d) (N (L 0x10000000000000000000000000183c2) (L 0xffffffffffffffffffffffffff7b26)))) (N (N (L 0x1000000000000000000000000002e3e) (N (L 0xfffffffffffffffffffffffffff05a) (L 0x100000000000000000000000000055f))) (N (L 0xfffffffffffffffffffffffffffe35) (N (L 0x100000000000000000000000000009a) (L 0xffffffffffffffffffffffffffffce))))) (N (N (N (L 0x1000000000000000000000000000010) (N (L 0xfffffffffffffffffffffffffffffb) (L 0x1000000000000000000000000000001))) (N (zL) (N (zL) (zL)))) (N (N (zL) (N (zL) (zL))) (N (zL) (N (zL) (zL)))))))

private def cneg_lf_2 : FastDTree := dleaf cneg_bt_2 0xffffffffffedcdd22354e347751418 0x10000000000633c465ae0e50c666f9f 0x100000000001518f8ff503f435f10bf 0x1000000000019e2bb98d93b3daf16ff 0x64e3cf48207c857c40ad 0x2164ecc507822b66533b (M 0xffffffffffe8ff7c91eeab0800849d 0x100000000005ab79e9be5d83845619b 0x1000000000012b482591279d575ee7d 0x100000000001a285dc07a08fbeae5ba 0x1000000000043bc2ee564db9867fd4f 0x100000000008430e570b5611c4288a4 0x1000000000089c6d78eb4434e0e70ba 0x1000000000042b72ddb168ae277e69e 0x20285303ff0fcb645298 (Q 0x5d9687a45ede9c31b168 0x9488d68d4888ad4c7eff 0x9914669c067d2802b5d6)) (M 0xffffffffffe2716cc7606a311006cd 0x100000000004b3fc82381aeb03665cd 0x100000000000e3c2c91538995ee051e 0x100000000001a1d4935ae61ee1f1382 0x1000000000026e7f3b4e5d9044df82c 0x100000000007347ff90e45627e41a5c 0x100000000005f646f1e2a25d3033caa 0x100000000004340b00de3d5455dbfcf 0x1dbe014dce6bebc883b8 (Q 0x50d887f68a64e3547c72 0x79ab5f28658ae1964a22 0x74b74a6f6c1bfe100c61)) (M 0xffffffffffdee6fbbf50ab86fe36b6 0x100000000003dde9d48a761a62535b9 0x100000000000a40884d941203d55f2f 0x1000000000019706e6c75b12f8f5806 0x1000000000012fa0d5eb9b7a06bf69a 0x1000000000062fd15f78d72905f11e1 0x1000000000041ccf8b66e5793fc5ed1 0x100000000003e94763d4a5737c07f1a 0x1b6d64701cb516f7aea8 (Q 0x462a90ccb523f3e434f8 0x64ca8bada21d8e8be263 0x5aceaf2b3a944648c575)) (M 0xffffffffffdd70c7830b142244dd61 0x100000000003270eb114db3a00103c0 0x1000000000006cb2193208a8afc5ae0 0x10000000000184ccb4e0f2375e9d423 0x10000000000054665298e99cbdc23e5 0x100000000005423c3a86bd9742eb852 0x100000000002d04fb60b6b06b630398 0x1000000000038116b1ce07fb97c813b 0x193b5310dce4dbb5b473 (Q 0x3d25034e04109c57611a 0x544e0dd6d56c2681b827 0x47e7c44e7e257ff457dc))

private def cneg_bt_4 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffffe8702461001404c146361) (L 0x10000000005959526d503deb34e3aa2))) (N (L 0xfffffffff8d7482b98efb7af5ad559) (N (L 0x1000000000f334933911a1e8c26f57b) (L 0xffffffffeea30775657cf6c8097609)))) (N (N (L 0x1000000001b0fe38ef61647b2ed6ae8) (N (L 0xffffffffe3fb9613d5ec231b4ffcea) (L 0x100000000239a2809f4f0e62a6c9536))) (N (L 0xffffffffde28492fd6b6af15a99ca2) (N (L 0x100000000250693f65d0034820a58a6) (L 0xffffffffdf5a90a22ec46922b0acc8))))) (N (N (N (L 0x1000000001fc68b895b5ef579bbdbb2) (N (L 0xffffffffe5cc9d1cbfa046f92fcccc) (L 0x100000000172ee1c70791ffdedc3895))) (N (L 0xffffffffee00e99d82dace45db8be9) (N (L 0x1000000000eb266f0b4181f231579ff) (L 0xfffffffff5330950af290bac68becb)))) (N (N (L 0x100000000083b68bb8c4a1e8c9d328d) (N (L 0xfffffffffa3ef155223f5756cb4c3e) (L 0x1000000000420cc016a2fc2dfa321fa))) (N (L 0xfffffffffd3e94ff60cbc16b25c288) (N (L 0x10000000001df8b78946602cb153def) (L 0xfffffffffecd43574fb9af7572a290)))))) (N (N (N (N (L 0x10000000000c6a683acf65e71e9f0a7) (N (L 0xffffffffff85df8b6c1c9a7b4134e2) (L 0x100000000004bae4845bb5dee55035c))) (N (L 0xffffffffffd329cfcb4e5f824baaf1) (N (L 0x100000000001aaf209ffae1b536399e) (L 0xfffffffffff0baeb2a230a147b94e1)))) (N (N (L 0x1000000000008c1398d8f04e5abe98d) (N (L 0xfffffffffffb26a370915017d074c7) (L 0x1000000000002af78a216591981ce3b))) (N (L 0xfffffffffffe8ec4bd60f94db8f085) (N (L 0x1000000000000c5f8507b56b32168e0) (L 0xffffffffffff98b9a649337173c7a9))))) (N (N (N (L 0x100000000000035b791e0fef69a47af) (N (L 0xffffffffffffe4bdbab9fa2fb91469) (L 0x10000000000000dc7618d1fc6837c26))) (N (L 0xfffffffffffff9307007ed07cdb44c) (N (L 0x10000000000000359d9d65a7d773bad) (L 0xfffffffffffffe62747100e64e9d38)))) (N (N (L 0x100000000000000c6533933c8dc9884) (N (L 0xffffffffffffffa2a6e939dee34e08) (L 0x1000000000000002bb0d3a9659b742d))) (N (L 0xffffffffffffffebe68f4261545450) (N (L 0x10000000000000009310f2e1a4919ac) (L 0xfffffffffffffffbdcf9d9347c9ba3))))))) (N (N (N (N (N (L 0x10000000000000001d9b066cb95c369) (N (L 0xffffffffffffffff2f3fd68a59fa93) (L 0x100000000000000005b6988f39cae77))) (N (L 0xffffffffffffffffd885aa5a78b70b) (N (L 0x1000000000000000010f07935d22673) (L 0xfffffffffffffffff8d356f7473830)))) (N (N (L 0x100000000000000000304d52d14279b) (N (L 0xfffffffffffffffffebec356ad9621) (L 0x100000000000000000084a71bb9eca4))) (N (L 0xffffffffffffffffffc9d9ea2365dc) (N (L 0x100000000000000000015f579bc170a) (L 0xfffffffffffffffffff73122635b47))))) (N (N (N (L 0x1000000000000000000038290662926) (N (L 0xfffffffffffffffffffe9d9f533192) (L 0x1000000000000000000008ada9800c7))) (N (L 0xffffffffffffffffffffca2100fe65) (N (L 0x10000000000000000000014c4110c4f) (L 0xfffffffffffffffffffff81209c522)))) (N (N (L 0x1000000000000000000000302362ab9) (N (L 0xfffffffffffffffffffffede63c6b3) (L 0x100000000000000000000006c362d26))) (N (L 0xffffffffffffffffffffffd7ea4e86) (N (L 0x100000000000000000000000ec19697) (L 0xfffffffffffffffffffffffa9cded7)))))) (N (N (N (N (L 0x1000000000000000000000001f467ec) (N (L 0xffffffffffffffffffffffff4be02e) (L 0x10000000000000000000000004071d7))) (N (L 0xffffffffffffffffffffffffe91ea6) (N (L 0x100000000000000000000000008132f) (L 0xfffffffffffffffffffffffffd2bd8)))) (N (N (L 0x100000000000000000000000000fc31) (N (L 0xffffffffffffffffffffffffffa8ce) (L 0x1000000000000000000000000001df9))) (N (L 0xfffffffffffffffffffffffffff5c5) (N (L 0x1000000000000000000000000000379) (L 0xfffffffffffffffffffffffffffed6))))) (N (N (N (L 0x1000000000000000000000000000064) (N (L 0xffffffffffffffffffffffffffffe0) (L 0x100000000000000000000000000000a))) (N (L 0xfffffffffffffffffffffffffffffd) (N (L 0x1000000000000000000000000000001) (zL)))) (N (N (zL) (N (zL) (zL))) (N (zL) (N (zL) (zL)))))))

private def cneg_lf_4 : FastDTree := dleaf cneg_bt_4 0xfffffffffffae4c560ad2318f98ed0 0x10000000000560b951d95be338806ae 0x10000000000174ebc025e419ab7ab99 0x100000000001290ac1bac3ff223d5b9 0x5632560f6e028cfdaf02 0x1dcc39e5fe2197b1ddba (M 0xfffffffffff656160ce64c4f9ec1f9 0x100000000004eda6384f94c446ac4cc 0x10000000000153432fbef2c04894a51 0x10000000000131f8a09a2b63eb90b82 0x1000000000040ba87251513f131d676 0x100000000006f5c3f11d47cf5bad103 0x100000000007ac8235b0b880efe4232 0x100000000003c25d5dba6441a4a10c1 0x1c8db26f5924aa26f0c3 (Q 0x4f716b1859ed001f9adc 0x80ce458e163530ee4a9e 0x88b909fcbf8a72a35230)) (M 0xffffffffffeff0a668dd6c737503fd 0x1000000000041e044b8352714ff1722 0x10000000000113ae5af49aabe604a11 0x1000000000013adcfcded9beab0d484 0x10000000000273cb6126338e6907897 0x1000000000060530127f26d670b2dca 0x1000000000053a9d71d9c872b61a37e 0x100000000003b023158436e10675af6 0x1a27f0036b928aa3ba88 (Q 0x43ce30db1cbbd05b14a4 0x68025af2f379979be35c 0x66612d944edb7545c897)) (M 0xffffffffffec30d4bf84de4ce66d36 0x1000000000036bb7cfae86e59c73593 0x100000000000da33b27cadfa84abc7f 0x10000000000139f5b73480cef2e64ca 0x1000000000015db2670c84046be20c9 0x100000000005233c20eb56a72cbe93b 0x1000000000039162684f9cb3637efa3 0x100000000003597e95a08b4a2ae6dd2 0x17e56b8cd1be30eb783d (Q 0x3a34f5a0a311f383bf36 0x550ee1ee2855f17ac1d6 0x4e4d2f3b507cd10c8bca)) (M 0xffffffffffea3f44e2a95e96e23bd8 0x100000000002d42bd3adb9750d5f52c 0x100000000000a784962763a29474146 0x10000000000131ac637d5a44f1c2d03 0x1000000000009ff15c7a7978a9406e2 0x10000000000459e907aa315aced40a3 0x1000000000026ec7ec4e78a3f0db6fb 0x100000000002f04e094db3e354834d5 0x15c90ff67d73cfb08575 (Q 0x32377a71e806732f5556 0x46555a83419bd2cdaf11 0x3d0a2f1113c92d13c3b1))

private def cneg_bt_6 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffffdf03662166826d0e957ef) (L 0x10000000006a00fdb788cb47e28b05b))) (N (L 0xfffffffff54310591bf2aa754cc97a) (N (L 0x1000000001470fd41e870380f85390d) (L 0xffffffffe43e2ce41a33836e401b36)))) (N (N (L 0x100000000283320de42359476c1781c) (N (L 0xffffffffd078f3c613a3684f2b9f27) (L 0x1000000003979130aab714147eba446))) (N (L 0xffffffffc34e90071eb818938d919c) (N (L 0x100000000403d12f6a608307800ef9b) (L 0xffffffffc24d5726089bf6a07b1486))))) (N (N (N (L 0x1000000003ac76ba22a49d4765ff2f4) (N (L 0xffffffffcbf6dd74c570bc7ea4874d) (L 0x1000000002d730a6f3c7cd67ed29335))) (N (L 0xffffffffda8825048400bbf79afe91) (N (L 0x1000000001e64a9bec75b66885c92a1) (L 0xffffffffe87a5c7789f24f593e6bff)))) (N (N (L 0x10000000011e4088b4383a7a8b6257f) (N (L 0xfffffffff2eaab8df64e0bfde80c9e) (L 0x10000000009664693df67840ccf0f31))) (N (L 0xfffffffff978565ca4fd825750e666) (N (L 0x10000000004750a73e2c18fe6d3a303) (L 0xfffffffffd0b9738b42776d4d8f38e)))))) (N (N (N (N (L 0x10000000001ecde3a965ebc09edeb3e) (N (L 0xfffffffffec70c2249e9a97d666300) (L 0x10000000000c36c7b95d26d7ddebd5d))) (N (L 0xffffffffff88c2a0f170ea22911d7c) (N (L 0x1000000000047983321baeb20c7e849) (L 0xffffffffffd5e79e8093929c1d694f)))) (N (N (L 0x10000000000185f09bbc28c94ee53d5) (N (L 0xfffffffffff2287169f39f7884c853) (L 0x1000000000007bf07e74c10a2d4c4df))) (N (L 0xfffffffffffbbdaf90f8279af2354d) (N (L 0x10000000000024f08a12ccc3794766f) (L 0xfffffffffffec4d19887e2f5bec1d1))))) (N (N (N (L 0x1000000000000a5cef4c30c5a36f8da) (N (L 0xffffffffffffaa1865fa0e3ffa3355) (L 0x10000000000002bee5e8bde7e0fe5b2))) (N (L 0xffffffffffffe9da7e8fc5517c02ea) (N (L 0x10000000000000b06a63cb7a66f9a99) (L 0xfffffffffffffa9589d965ac42fa2e)))) (N (N (L 0x100000000000002a0e944cec5a50c45) (N (L 0xfffffffffffffebd8c0ebcae6e0b8b) (L 0x10000000000000098bff4a7f6136182))) (N (L 0xffffffffffffffb882de33787226b7) (N (L 0x100000000000000211702c7654fd0d1) (L 0xfffffffffffffff0dbf1bc843467c0))))))) (N (N (N (N (N (L 0x10000000000000006dacbfac8964b69) (N (L 0xfffffffffffffffcee3d0e1908ed60) (L 0x100000000000000015c4356e02f35aa))) (N (L 0xffffffffffffffff6741f8eda33c39) (N (L 0x1000000000000000042550792ffa340) (L 0xffffffffffffffffe37b7b053c6a95)))) (N (N (L 0x100000000000000000c24e610de6528) (N (L 0xfffffffffffffffffae0d52f0e3244) (L 0x100000000000000000223ea6f61a039))) (N (L 0xffffffffffffffffff1d27d9f341a0) (N (L 0x10000000000000000005d15b751363f) (L 0xffffffffffffffffffda24d76b33cc))))) (N (N (N (L 0x10000000000000000000f4374faf79a) (N (L 0xfffffffffffffffffff9e617dca3d3) (L 0x1000000000000000000026b2630bed3))) (N (L 0xffffffffffffffffffff0c9bdd8829) (N (L 0x1000000000000000000005ee88a25ae) (L 0xffffffffffffffffffffdb4a150506)))) (N (N (L 0x1000000000000000000000e16bb347d) (N (L 0xfffffffffffffffffffffaa29c141a) (L 0x1000000000000000000000207003924))) (N (L 0xffffffffffffffffffffff3d5ad1a0) (N (L 0x100000000000000000000004876222c) (L 0xffffffffffffffffffffffe538f933)))))) (N (N (N (N (L 0x1000000000000000000000009d30e3d) (N (L 0xfffffffffffffffffffffffc6bd454) (L 0x10000000000000000000000014b68f6))) (N (L 0xffffffffffffffffffffffff88f30e) (N (L 0x10000000000000000000000002a79b5) (L 0xfffffffffffffffffffffffff0f29f)))) (N (N (L 0x1000000000000000000000000054c81) (N (L 0xfffffffffffffffffffffffffe259c) (L 0x100000000000000000000000000a4d4))) (N (L 0xffffffffffffffffffffffffffc719) (N (L 0x1000000000000000000000000001385) (L 0xfffffffffffffffffffffffffff959))))) (N (N (N (L 0x1000000000000000000000000000240) (N (L 0xffffffffffffffffffffffffffff3f) (L 0x1000000000000000000000000000040))) (N (L 0xffffffffffffffffffffffffffffec) (N (L 0x1000000000000000000000000000006) (L 0xfffffffffffffffffffffffffffffe)))) (N (N (zL) (N (zL) (zL))) (N (zL) (N (zL) (zL)))))))

private def cneg_lf_6 : FastDTree := dleaf cneg_bt_6 0x1000000000003c14886151269462675 0x100000000004832bdd52b2de581c0db 0x10000000000176135e4d2b25562b9cc 0x100000000000ba4d948946bcb585c48 0x484bb8c0c5c0c499aa78 0x1a1e6bb36e80b3683be5 (M 0xffffffffffff96f7dba335c6859a0d 0x1000000000042274a6755c9a653ba4b 0x100000000001596f1d19cd6ab2b5f23 0x100000000000c6727304932199bc7c3 0x100000000003b5e82f3f59239ceab84 0x100000000005d4498c59409679a3a17 0x100000000006ca681a4404dac595643 0x10000000000377d0c6d2e4cb65d9e5e 0x18e6112a1e89bb9a60cc (Q 0x42279e08a97f01ef7b79 0x6e8f799f9c7dadd5e294 0x79ffe0f8bce9d4c1e0be)) (M 0xfffffffffff9a86a28e0ff5d53de0c 0x10000000000375ae0a747c86d80fb6c 0x10000000000122c4215e0d6fb18c4e4 0x100000000000d65a2d85bac0259a61a 0x10000000000250b8f6abd71aea1f6ea 0x100000000004fa182a7131081fca120 0x100000000004870313b7dec3f67cff9 0x1000000000034a4415a2d3d02199522 0x1693c933666ae3526b17 (Q 0x37b79586155e23ae0aad 0x57d37ba2959d0a022d07 0x598bb65c1041257331e0)) (M 0xfffffffffff6058897e8fb375d6f64 0x100000000002e3173ac829c7067a894 0x100000000000f0b7e8880155a131f11 0x100000000000dcff61b963386879c38 0x1000000000016207ec066b01ee7c9cf 0x1000000000043386d105862d220af67 0x10000000000308f218f6903ae5445ed 0x100000000002e64a19f12f969ea0dde 0x146c7be983066409eac9 (Q 0x2f42354392c6586cea93 0x46c4bee8ac40890fe4db 0x4328a81454a3541c922b)) (M 0xfffffffffff3ec74b1f66a60143b3e 0x10000000000267ae0be7a8d9ec236f7 0x100000000000c40a5e346a46e682ea6 0x100000000000dc88a7ee7c7f3b7dc73 0x100000000000c18e8ac743821b33203 0x100000000003879292a130ca82b1f1d 0x1000000000020bf49c06ab6d65122d5 0x10000000000279f20e7c27521a45aec 0x1271242ce619441840e5 (Q 0x28549ad9f351c6670705 0x39c123f297e06cf243fd 0x33672066801b3039827f))

private def cneg_sub_0 : FastDTree := (dsplit (dsplit cneg_lf_0 cneg_lf_2) (dsplit cneg_lf_4 cneg_lf_6))

private def cneg_bt_9 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffffd596a7e1ccf0d55be4c7c) (L 0x10000000008035e21a7edd18ca14d54))) (N (L 0xfffffffff0f7b70917ff1354a5f5f8) (N (L 0x1000000001bfdc1f7f3603129033fac) (L 0xffffffffd61a348ab5ff0b15c17166)))) (N (N (L 0x1000000003c7f25c2ee52c65ccdaf12) (N (L 0xffffffffb3391c4f57b65d8a7972c7) (L 0x1000000005d7f7d32e4067d93108504))) (N (L 0xffffffff97af86f3b0c35ab384f7f6) (N (L 0x1000000006fcc8b839ea790d2e94191) (L 0xffffffff8fb610efa617ca6d5396f1))))) (N (N (N (L 0x1000000006ca730e5e94053f88b9082) (N (L 0xffffffff9c1b69449995b9c77c7f89) (L 0x10000000058c3086e019830a6fdbe4c))) (N (L 0xffffffffb460f491ac52dc8cda7a05) (N (L 0x1000000003e74eae14286c314e7875e) (L 0xffffffffce3a0722e836d616686d5a)))) (N (N (L 0x100000000268ede78ded3a89916b24a) (N (L 0xffffffffe30b3aa5cecdc6cccbadda) (L 0x1000000001530598107c344a034330f))) (N (L 0xfffffffff0ea6947d2a52e170fda1d) (N (L 0x1000000000a7c52ff236a8d493bb3cb) (L 0xfffffffff8e3942ce35df953133bfd)))))) (N (N (N (N (L 0x10000000004b7ae51fd59089ff7933c) (N (L 0xfffffffffcf09976c928de4c2017a4) (L 0x10000000001f1e9620e6db97852cc62))) (N (L 0xfffffffffec9fbefc648b69de62b8a) (N (L 0x10000000000bd644b8a67a0d592a10f) (L 0xffffffffff8e7a1c38d7862e11647d)))) (N (N (L 0x1000000000042d91e5254663106fe0e) (N (L 0xffffffffffd953627f3b0df2c93767) (L 0x1000000000016012e80f7d7afdfcf40))) (N (L 0xfffffffffff3af59131202a8b2a172) (N (L 0x1000000000006c8eca44342067a93d9) (L 0xfffffffffffc51c5bae71367ec72c3))))) (N (N (N (L 0x1000000000001f79bbb8987dc5311bf) (N (L 0xfffffffffffef6bb000fceba266848) (L 0x100000000000089c79cab43c986794f))) (N (L 0xffffffffffffb96b61a7a8487c2aad) (N (L 0x100000000000023ad7bbe1378dcd277) (L 0xffffffffffffee33390d1546ce8fdc)))) (N (N (L 0x100000000000008c4c39117401e1b89) (N (L 0xfffffffffffffbbbe0d98d4018eee5) (L 0x1000000000000020cf319ade590e0ae))) (N (L 0xffffffffffffff06a750fafc76527e) (N (L 0x1000000000000007513718449691d77) (L 0xffffffffffffffc9a661ecbd4bc8ac))))))) (N (N (N (N (N (L 0x10000000000000018f4006adff06c83) (N (L 0xfffffffffffffff4aadece93a7555e) (L 0x1000000000000000517a451bda6a288))) (N (L 0xfffffffffffffffdbc47812651c47b) (N (L 0x10000000000000000ff2e8a2811fc22) (L 0xffffffffffffffff90cb582aeeb8e3)))) (N (N (L 0x100000000000000002ffd355eaea1f1) (N (L 0xffffffffffffffffeb7d6892559653) (L 0x1000000000000000008aef0ff0c7648))) (N (L 0xfffffffffffffffffc5b957c333426) (N (L 0x1000000000000000001838d7106f906) (L 0xffffffffffffffffff605af4db1ba3))))) (N (N (N (L 0x1000000000000000000412f8e25a13f) (N (L 0xffffffffffffffffffe59cfe495f89) (L 0x10000000000000000000a972ffb5962))) (N (L 0xfffffffffffffffffffbc8ed14dc1c) (N (L 0x100000000000000000001a9f4088999) (L 0xffffffffffffffffffff5938221f6a)))) (N (N (L 0x10000000000000000000040c868deb2) (N (L 0xffffffffffffffffffffe7089b1a2c) (L 0x100000000000000000000098c23ac14))) (N (L 0xfffffffffffffffffffffc60720022) (N (L 0x100000000000000000000015d5ede77) (L 0xffffffffffffffffffffff7d61149a)))))) (N (N (N (N (L 0x10000000000000000000000307aee32) (N (L 0xffffffffffffffffffffffee22bcce) (L 0x100000000000000000000000689410f))) (N (L 0xfffffffffffffffffffffffda01222) (N (L 0x1000000000000000000000000db5a0f) (L 0xffffffffffffffffffffffffb16466)))) (N (N (L 0x10000000000000000000000001bfb2f) (N (L 0xfffffffffffffffffffffffff61b18) (L 0x10000000000000000000000000379c7))) (N (L 0xfffffffffffffffffffffffffec973) (N (L 0x1000000000000000000000000006bb1) (L 0xffffffffffffffffffffffffffdae4))))) (N (N (N (L 0x1000000000000000000000000000cb4) (N (L 0xfffffffffffffffffffffffffffbae) (L 0x1000000000000000000000000000176))) (N (L 0xffffffffffffffffffffffffffff83) (N (L 0x1000000000000000000000000000029) (L 0xfffffffffffffffffffffffffffff3)))) (N (N (L 0x1000000000000000000000000000004) (N (L 0xffffffffffffffffffffffffffffff) (zL))) (N (zL) (N (zL) (zL)))))))

private def cneg_lf_9 : FastDTree := dleaf cneg_bt_9 0x1000000000008cea5d86951183c0a0e 0x100000000003ad7425896a98d98a3ba 0x1000000000015baa77ac02147f307dc 0x1000000000005b66f296d16c659ba6b 0x3b7f0f48b3263856953d 0x1677aeac9621ab81751a (M 0x100000000000520bfd51e94b64e80ac 0x1000000000035c1dd5d7655833e5a5e 0x1000000000014411be8825c221f4c75 0x1000000000006973ab8534edb7d3df9 0x10000000000346fd73d651f1ab99d8b 0x100000000004e0e65dc1c48468c25e9 0x100000000005f946b7238ef4638847f 0x10000000000346f19a18ef7c437471d 0x154cb74c84d8b3f16f50 (Q 0x360055f77684a23c5845 0x5e08b8056443b54edcfc 0x6d047adf1c2a58268879)) (M 0xffffffffffffdf32e206c3f3d239ab 0x100000000002ccd6f14af0f8f3f0de2 0x1000000000011690bdf4c12d2b8fe42 0x1000000000007ddb0966f0d5e504b54 0x10000000000210eb25e246754e3093f 0x10000000000416a0c437b6b30d026ae 0x100000000003df0bc374b7d8b234a17 0x100000000002fe4039e16c79f5bad06 0x131ad49297bc24d53994 (Q 0x2ccd7b56c04af59a4f12 0x494aed26846b679a07f2 0x4e4b8dccd1d465bf0521)) (M 0xfffffffffffc9537b959e2bfc53e50 0x10000000000255686cf377256629ba9 0x100000000000ec6e51597c639b75847 0x10000000000089b1782a15a84a68819 0x100000000001475583ddce79123c9bc 0x100000000003650f382ed172d18b3ce 0x100000000002875da3c87dcd78f9a6a 0x1000000000028c2dab64b421752dd18 0x1119a94dfa28968e8423 (Q 0x257e793d2ab885ac851e 0x3a0a95378a95f0a6bd4e 0x396ec425a6a129c19636)) (M 0xfffffffffffa940b2ee899ef8cfbd1 0x100000000001f25cf219fa0c63e8d20 0x100000000000c670437614eea995c34 0x1000000000008edf31c97f7de39dae1 0x100000000000c2f41cb5064e6878f82 0x100000000002d05fafe3f6eb9ce498b 0x100000000001abe0c8f2a0652b3811c 0x1000000000021b35d9090201a4d25ee 0xf4853d3c4230845cdfe (Q 0x1f9db4abb7eeca6829f2 0x2ea49a8fb3c248230cf8 0x2b059f0ab493168c4552))

private def cneg_bt_11 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffffce85193219c3a395e03e6) (L 0x100000000094823adcf3c961bdb8cce))) (N (L 0xffffffffed278c51214437c932520a) (N (L 0x1000000002374396bfb034f71df78d7) (L 0xffffffffc8265512221de321ea6764)))) (N (N (L 0x10000000051f79af08dab3173735b0c) (N (L 0xffffffff93fb02f6b51caff1be2d4f) (L 0x10000000085f82eb413dcd7627c3017))) (N (L 0xffffffff65f2713091e67c5f7a2115) (N (L 0x100000000a836a65506194900d065fb) (L 0xffffffff52aa68eabe652c37dfdd46))))) (N (N (N (L 0x100000000aad4736445b6a0f5eee287) (N (L 0xffffffff5f5c86f956cedff577d8e0) (L 0x100000000914d9d7e334be51a3601c2))) (N (L 0xffffffff81a8feb4bd5fe4fade740f) (N (L 0x1000000006a26f734caeeb2a15c642c) (L 0xffffffffa9cdc73ab296b28c02e55a)))) (N (N (L 0x10000000043e296b9bee06e27d840ac) (N (L 0xffffffffcc1efaf8ceb8ff4485289e) (L 0x1000000002691f2341e135cc3ede956))) (N (L 0xffffffffe416136afa4dbc471a663b) (N (L 0x10000000013b3d536b175ae8cc72dc0) (L 0xfffffffff26d976820553edbe99818)))))) (N (N (N (N (L 0x1000000000923214ec19e46da937c12) (N (L 0xfffffffff9fbdcade5535a2b70580b) (L 0x10000000003e0e302b5e89983caae97))) (N (L 0xfffffffffd8ce5eec88211ac0d2171) (N (L 0x100000000018467485b658da952ae22) (L 0xffffffffff13f6ad47847dcb096afc)))) (N (N (L 0x100000000008cda3d37a8eea872c104) (N (L 0xffffffffffad6c0ed7c336d7af103a) (L 0x100000000002f985c46229e2f285d46))) (N (L 0xffffffffffe504bcafe74b2e795cc2) (N (L 0x100000000000f0d877642f99186f564) (L 0xfffffffffff7bb5bf8e912d25cdb8c))))) (N (N (N (L 0x1000000000004793539f0fb93433898) (N (L 0xfffffffffffd9d6c6eba93dfc8c0d4) (L 0x100000000000140ec57aa6a2638d6e1))) (N (L 0xffffffffffff59a66f6631a45f95dd) (N (L 0x10000000000005511944296b3385890) (L 0xffffffffffffd5115527c0ff95c8d7)))) (N (N (L 0x10000000000001563e0f815c15b0475) (N (L 0xfffffffffffff579cf3d4b1983ce3a) (L 0x1000000000000051d6cd7aa5238d74f))) (N (L 0xfffffffffffffd8b2cd6521a44ea21) (N (L 0x1000000000000012a777d2aeeab6ded) (L 0xffffffffffffff73f2be7d3ea91517))))))) (N (N (N (N (N (L 0x10000000000000040fc542d5100060c) (N (L 0xffffffffffffffe22cc0108d645c8b) (L 0x1000000000000000d8ac7ba6c7e439c))) (N (L 0xfffffffffffffff9ea62f7cd3ac0bc) (N (L 0x10000000000000002b4a722a3d9d3e4) (L 0xfffffffffffffffecf157a7404f0cc)))) (N (N (L 0x1000000000000000084e77e236bf132) (N (L 0xffffffffffffffffc6a1bc63eccd4b) (L 0x10000000000000000188715de3e2b75))) (N (L 0xfffffffffffffffff59c729bd53206) (N (L 0x10000000000000000045c254a07ff8c) (L 0xfffffffffffffffffe2fcd6b810eb5))))) (N (N (N (L 0x1000000000000000000bf58efa5f659) (N (L 0xffffffffffffffffffb1cfa6378f10) (L 0x10000000000000000001fad1d4bd3f9))) (N (L 0xfffffffffffffffffff34677527b02) (N (L 0x10000000000000000000511bfe1fb4c) (L 0xfffffffffffffffffffdff36bc3a27)))) (N (N (L 0x100000000000000000000c8fe371b94) (N (L 0xffffffffffffffffffffb1d750f2a8) (L 0x1000000000000000000001e28126ff9))) (N (L 0xfffffffffffffffffffff4742a99fb) (N (L 0x10000000000000000000004632a58b6) (L 0xfffffffffffffffffffffe58655405)))))) (N (N (N (N (L 0x100000000000000000000009e97108a) (N (L 0xffffffffffffffffffffffc50e7432) (L 0x1000000000000000000000015c0534e))) (N (L 0xfffffffffffffffffffffff807a74a) (N (L 0x1000000000000000000000002e66e2e) (L 0xfffffffffffffffffffffffef3b33e)))) (N (N (L 0x1000000000000000000000000604d6d) (N (L 0xffffffffffffffffffffffffddaa16) (L 0x10000000000000000000000000c294b))) (N (L 0xfffffffffffffffffffffffffbb87c) (N (L 0x1000000000000000000000000017f03) (L 0xffffffffffffffffffffffffff7af1))))) (N (N (N (L 0x1000000000000000000000000002def) (N (L 0xfffffffffffffffffffffffffff03f) (L 0x100000000000000000000000000055f))) (N (L 0xfffffffffffffffffffffffffffe2f) (N (L 0x100000000000000000000000000009c) (L 0xffffffffffffffffffffffffffffcc)))) (N (N (L 0x1000000000000000000000000000010) (N (L 0xfffffffffffffffffffffffffffffb) (L 0x1000000000000000000000000000001))) (N (zL) (N (zL) (zL)))))))

private def cneg_lf_11 : FastDTree := dleaf cneg_bt_11 0x100000000000a8326ab25985079e955 0x1000000000031abe2e443dbff6e3910 0x1000000000013b17837d5a82b1199b9 0x1000000000002244508c8a1f0f4512c 0x32c58a1054162723123d 0x13cf321c636137f39947 (M 0x10000000000073b3f1df7d0b4acd04c 0x100000000002d3064461172573fedf0 0x100000000001271b83b0ae5d2ffb892 0x10000000000030f932fe9e65fb58dec 0x100000000002ea50aa6a0c0f670947c 0x10000000000448255fc3ef217d0057f 0x10000000000568c3a53b0eba6cb992a 0x10000000000330219f8af98460abd3d 0x12b24bfa1e2497034903 (Q 0x2dc3949b7b2aaaef41c3 0x52e17cb0bb064b846f54 0x6475f10553e9642a18a1)) (M 0x1000000000002913c0baf18ed169b27 0x100000000002565e2f560e0bd4a132b 0x1000000000010042e3ef3ca592b3038 0x100000000000473ee8b6b17d7796df3 0x100000000001d4e66cdc8391bd2bbe8 0x10000000000386489dfcfb88f87b3bf 0x1000000000036a338e11448a67f3b62 0x100000000002d3895d689a9b81ad247 0x109fb1ce30e8a234c7b2 (Q 0x257c6b938b746b32aee8 0x3f8d984b5931e92fcc45 0x46ec88f3044f84820c02)) (M 0xffffffffffffa44ace84a83d2b1eaa 0x100000000001f03ee342f993bb3c3a7 0x100000000000dc009a59d7800a6a0cb 0x100000000000558a06ed94d8e0cfbf8 0x100000000001253c085f20de4542c74 0x100000000002e0e5b2b31d914eec1e2 0x1000000000022c66116733111d676f6 0x10000000000256bf7d6e0ebeae13931 0xec0bf1854383cfa556d (Q 0x1f0476090c1d528d986b 0x319190b657746a54a879 0x3315c63af7c9fb1a404f)) (M 0xfffffffffffdd288c05daf750d3a8d 0x1000000000019cdb99d81370e5a8752 0x100000000000bb1a130a266013ab5c0 0x1000000000005d9798775248e7ea85f 0x100000000000b4b21f9b3c01d257559 0x1000000000025a312ac5d1456fb153d 0x100000000001677eda36b2401baf1b4 0x100000000001e1b518b202df162e037 0xd1346b3629530509e5a (Q 0x19e534ff2250d4f2895b 0x274b7cfcaadead5110e5 0x25910a50e9001523f85c))

private def cneg_bt_13 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffffc9ceba124cfad7bc87e2c) (L 0x1000000000a3c697e0fcf5a15ce78ba))) (N (L 0xffffffffea484a4b0e852754e65dfb) (N (L 0x100000000296ba70e26ce9a2ff9deef) (L 0xffffffffbcd98b9f4ec7669ec5932b)))) (N (N (L 0x10000000064099340ec62fa5cb4c2cb) (N (L 0xffffffff794280b9bee3709bd72fc1) (L 0x100000000a9969581c4384808da4ba2))) (N (L 0xffffffff39700149ac2d2cccfa246a) (N (L 0x100000000dbe2129a37a14b1fd125dc) (L 0xffffffff19d5cf39180961086294f1))))) (N (N (N (L 0x100000000e5e07ceed49abd0d698670) (N (L 0xffffffff24c3492aebf2d858b4e0e0) (L 0x100000000c8d1761cd075f62bd6654a))) (N (L 0xffffffff4f1cd0509341478937337b) (N (L 0x1000000009667ca4cd0a63e33cf576d) (L 0xffffffff84632adfc8c6b48765a3ed)))) (N (N (L 0x100000000627673244e73d48afe70ff) (N (L 0xffffffffb3e4ec02626f457464bc12) (L 0x100000000393263f6f7ab56acfbed2b))) (N (L 0xffffffffd6287af8b402b398a3a56e) (N (L 0x1000000001dd72b9db78c5f8fd24d31) (L 0xffffffffeb3b933971c1f92098471d)))))) (N (N (N (N (L 0x1000000000e1ef9d518a0d59893cbf5) (N (L 0xfffffffff69c5369034645abf39ec4) (L 0x100000000061c7720349176c511eb25))) (N (L 0xfffffffffc1a8523a1b10fb3efba34) (N (L 0x100000000026f863c55acaf7356ffd5) (L 0xfffffffffe819d002a97d6d77c1126)))) (N (N (L 0x10000000000e63aa93a9e616326231f) (N (L 0xffffffffff77d473c1de617ad8a5dd) (L 0x100000000004f2a32270c34b68dfb6e))) (N (L 0xffffffffffd2bcc8a57f140913beea) (N (L 0x100000000001976e1efe725031c194d) (L 0xfffffffffff1e595412afd99e6eff5))))) (N (N (N (L 0x1000000000007b167570aeb28fa271f) (N (L 0xfffffffffffbdd823490c1917ec72b) (L 0x100000000000230c8965a3884980c7f))) (N (L 0xfffffffffffedb07cac7bc6f96183d) (N (L 0x100000000000096fbd488b12058c736) (L 0xffffffffffffb3377e5b3a53a2525e)))) (N (N (L 0x1000000000000268bb4aa96e8374bf3) (N (L 0xffffffffffffece49636707f6f0f7f) (L 0x1000000000000095aecdff22d76928c))) (N (L 0xfffffffffffffb79752e2b4b7d9cb8) (N (L 0x10000000000000229e086b39d6d20e2) (L 0xfffffffffffffefa3c93d77331c87e))))))) (N (N (N (N (N (L 0x1000000000000007a52a22a010b9a97) (N (L 0xffffffffffffffc777376b928afde5) (L 0x10000000000000019d907688a573e90))) (N (L 0xfffffffffffffff44e86e7b336e665) (N (L 0x100000000000000053c3c44dc8c5cb0) (L 0xfffffffffffffffdae06674c34f99e)))) (N (N (L 0x1000000000000000104a0da1097a40b) (N (L 0xffffffffffffffff8ec10545e604dd) (L 0x1000000000000000030bc72275822cd))) (N (L 0xffffffffffffffffeb391b5ea1abee) (N (L 0x1000000000000000008c69ba2fcde11) (L 0xfffffffffffffffffc53abf952d58a))))) (N (N (N (L 0x10000000000000000018612bc465893) (N (L 0xffffffffffffffffff5f9aad37bb92) (L 0x10000000000000000004162c867f941))) (N (L 0xffffffffffffffffffe5922e117407) (N (L 0x10000000000000000000a97f4500807) (L 0xfffffffffffffffffffbc9e1154349)))) (N (N (L 0x100000000000000000001a923bf4293) (N (L 0xffffffffffffffffffff59af9473c8) (L 0x100000000000000000000408d6e5fee))) (N (L 0xffffffffffffffffffffe7235d1b11) (N (L 0x1000000000000000000000980a89073) (L 0xfffffffffffffffffffffc652a8000)))))) (N (N (N (N (L 0x100000000000000000000015b7e8cb5) (N (L 0xffffffffffffffffffffff7e1a5f9a) (L 0x10000000000000000000000303552e5))) (N (L 0xffffffffffffffffffffffee3c39cc) (N (L 0x1000000000000000000000006802643) (L 0xfffffffffffffffffffffffda33d8a)))) (N (N (L 0x1000000000000000000000000da472a) (N (L 0xffffffffffffffffffffffffb1beb5) (L 0x10000000000000000000000001bde91))) (N (L 0xfffffffffffffffffffffffff623c0) (N (L 0x1000000000000000000000000037752) (L 0xfffffffffffffffffffffffffeca15))))) (N (N (N (L 0x1000000000000000000000000006b90) (N (L 0xffffffffffffffffffffffffffdae7) (L 0x1000000000000000000000000000cb7))) (N (L 0xfffffffffffffffffffffffffffbac) (N (L 0x1000000000000000000000000000176) (L 0xffffffffffffffffffffffffffff82)))) (N (N (L 0x1000000000000000000000000000029) (N (L 0xfffffffffffffffffffffffffffff3) (L 0x1000000000000000000000000000004))) (N (L 0xffffffffffffffffffffffffffffff) (N (zL) (zL)))))))

private def cneg_lf_13 : FastDTree := dleaf cneg_bt_13 0x100000000000ad9dc73ce973beb894d 0x100000000002c1a5bb5f9a31b2a07e7 0x100000000001218ac41f8a259388dfc 0x10000000000003869c656dabea4ffa1 0x2d6b110338e939faa440 0x121904701e7fa9baba88 (M 0x1000000000007d7a168af7ffe980675 0x1000000000027f7a528717d1e218598 0x1000000000010fd31bdfea2fc0bc117 0x1000000000001259abfa313e41edeb6 0x100000000002aa74dbd86044fa16912 0x100000000003efcb446703d66aa67e5 0x1000000000050e8a6f9bdb9ba04a559 0x100000000003265ca88b2b98c169bc8 0x11071828f1e087498643 (Q 0x28bac0a059cfa4a24ea9 0x4c12044e3c3fa4a25ef6 0x5f52424cf0ee9698214d)) (M 0x10000000000039834a2be0f5a347c7c 0x1000000000020da2eb3fd939b8b381e 0x100000000000ed318b7e32354c7495f 0x100000000000293c8f2b82b46c7d8e1 0x100000000001a975d2643e09c0067b8 0x1000000000033221a15792aaadef240 0x100000000003210518214a1c7d4d60d 0x100000000002bcd2e78fa6a657565a2 0xf0c05f09d8cf4a0fd50 (Q 0x210c604d86915689bc56 0x39a25b088d788f9775ee 0x4285321572e912e8f5e6)) (M 0x1000000000000f136765bf42a734934 0x100000000001b1a27f2d7e996d4d260 0x100000000000ccb37c05178a87d6e7a 0x100000000000388dce89bf657ebafcc 0x1000000000010a0f215cec1cdc1da22 0x100000000002936a13d9ddc595019b9 0x100000000001f32e30c783a2bfe7af6 0x10000000000238f0860ab61f481d786 0xd45eaa0095b6188f1e4 (Q 0x1b1e594b7d1675541af9 0x2c710e5bffbe750851db 0x2f4e250046a4436e0728)) (M 0xffffffffffff48b56526214de51060 0x10000000000167726b193854f0dd276 0x100000000000af1c327f3f1f3750c42 0x10000000000041ef85ff18583bd3718 0x100000000000a60982b8dfff1094108 0x1000000000021497f0d38df2064eb4d 0x1000000000013c325b8101286315351 0x100000000001c1046c45d82848d7be5 0xbb1ccf1e70a4d6d7186 (Q 0x167a127b891dc2a85631 0x22ddff1f70e017a887ab 0x2252daebbdb7306ac3ad))

private def cneg_bt_15 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffffc5185af280320be32f873) (L 0x1000000000b46e432b3582fe0a8ee74))) (N (L 0xffffffffe71dd15f2457b0867717f4) (N (L 0x10000000030468c408708de271ad3c5) (L 0xffffffffafa9f0add822f1bf31fdd0)))) (N (N (L 0x10000000079b4ff812bed970db1be71) (N (L 0xffffffff58b353e453476f6d70ebb1) (L 0x100000000d5e92186f0510a9b196bfa))) (N (L 0xffffffff0132a7aac998174d0e17b5) (N (L 0x1000000011e538d82b98a61b63ebcb1) (L 0xfffffffecfb2262fb8bc69cbfab045))))) (N (N (N (L 0x100000001341aa730a64842bef3a801) (N (L 0xfffffffed612ed6bbb95b1cb3c8c4c) (L 0x1000000011469784bb1cbbb6341ea86))) (N (L 0xffffffff0967142c1ab77c5646c0ef) (N (L 0x100000000d4391c12f308b8cdf27b72) (L 0xffffffff4f7d2fa5d1cf462e11ca52)))) (N (N (L 0x1000000008e36a614316bc27d4d27d5) (N (L 0xffffffff90d5596884ded4a93ad582) (L 0x10000000054759841e1eff00146ad7d))) (N (L 0xffffffffc18ce88ea6ba61edba3f62) (N (L 0x1000000002d00880d5b6fe8ecd1ad84) (L 0xffffffffe05c1e41e6d6f3663d7073)))))) (N (N (N (N (L 0x10000000015bab4a2623076c953b09b) (N (L 0xfffffffff168ddd4fe4935b134678a) (L 0x100000000099670b1e7a2b38ce29cff))) (N (L 0xfffffffff9d4487c0e334cf43bd595) (N (L 0x10000000003e4a282e46932b71f3c06) (L 0xfffffffffd973859e2aa577f100fbe)))) (N (N (L 0x1000000000176ae43c5fc5c0bf0cf59) (N (L 0xffffffffff207017f13ea92469b3fa) (L 0x10000000000831975d852c73a5f760f))) (N (L 0xffffffffffb4671b4841be728febdc) (N (L 0x100000000002ae37770937a06935fb7) (L 0xffffffffffe80ca449d337f81fb63a))))) (N (N (N (L 0x100000000000d2be4718aa0a3b11a93) (N (L 0xfffffffffff8dd1490ba566b6826f2) (L 0x1000000000003cf9a816ed75136373f))) (N (L 0xfffffffffffdfe4ead661add9d4868) (N (L 0x10000000000010aca5cb0736ff0e18b) (L 0xffffffffffff774831ec392eb38c55)))) (N (N (L 0x100000000000045274ecace2f4df2d7) (N (L 0xffffffffffffdd76bef2eb96f0b9ee) (L 0x10000000000001108e4ca8e0428bdeb))) (N (L 0xfffffffffffff7b2f9720451f7048f) (N (L 0x100000000000003ff4acb83956da84e) (L 0xfffffffffffffe18ecbde1fa71f71b))))))) (N (N (N (N (N (L 0x100000000000000e539b94a310da9e0) (N (L 0xffffffffffffff95508bbd53ece34b) (L 0x100000000000000311dae9d441c2bae))) (N (L 0xffffffffffffffe9a0abcb29d18caf) (N (L 0x1000000000000000a15b43a792b27ee) (L 0xfffffffffffffffb8019e0443a93d4)))) (N (N (L 0x10000000000000001fcd1223199607a) (N (L 0xffffffffffffffff2172d72af4e09d) (L 0x100000000000000006067b6aba3091b))) (N (L 0xffffffffffffffffd6a2354e75d688) (N (L 0x100000000000000001195cc685befa5) (L 0xfffffffffffffffff897b307346172))))) (N (N (N (L 0x100000000000000000317a0151aa74f) (N (L 0xfffffffffffffffffeb870d1afdbc9) (L 0x1000000000000000000865d217bffcf))) (N (L 0xffffffffffffffffffc95a9c5e187c) (N (L 0x10000000000000000001609d3783415) (L 0xfffffffffffffffffff72f75687694)))) (N (N (L 0x1000000000000000000037f365aa344) (N (L 0xfffffffffffffffffffe9fb11e543a) (L 0x100000000000000000000898ee10b3f))) (N (L 0xffffffffffffffffffffcab50d52e2) (N (L 0x100000000000000000000147d28d025) (L 0xfffffffffffffffffffff82ea2ba1e)))))) (N (N (N (N (L 0x10000000000000000000002f5fae650) (N (L 0xfffffffffffffffffffffee307a1da) (L 0x100000000000000000000006a5d3edb))) (N (L 0xffffffffffffffffffffffd8951a7a) (N (L 0x100000000000000000000000e815585) (L 0xfffffffffffffffffffffffab3004f)))) (N (N (L 0x1000000000000000000000001ec82da) (N (L 0xffffffffffffffffffffffff4e7408) (L 0x10000000000000000000000003f93fe))) (N (L 0xffffffffffffffffffffffffe96205) (N (L 0x100000000000000000000000007fe56) (L 0xfffffffffffffffffffffffffd3168))))) (N (N (N (L 0x100000000000000000000000000fabe) (N (L 0xffffffffffffffffffffffffffa90e) (L 0x1000000000000000000000000001df5))) (N (L 0xfffffffffffffffffffffffffff5be) (N (L 0x100000000000000000000000000037d) (L 0xfffffffffffffffffffffffffffed3)))) (N (N (L 0x1000000000000000000000000000065) (N (L 0xffffffffffffffffffffffffffffdf) (L 0x100000000000000000000000000000a))) (N (L 0xfffffffffffffffffffffffffffffd) (N (zL) (zL)))))))

private def cneg_lf_15 : FastDTree := dleaf cneg_bt_15 0x100000000000aadab8ac02d6a25322c 0x100000000002705b0eb82c616995161 0x10000000000106496a69d6c1317e850 0xfffffffffffeab0f573dc972f731ba 0x2874f8aa0b264dd04fb4 0x10726a868cdc41862a5b (M 0x1000000000007f122880379627b4542 0x10000000000233166b23e0ff6b340e8 0x100000000000f6b1f8194ee8b010a49 0xffffffffffff969823761fe3e3c0d2 0x1000000000026a41a634481a5b6c6d2 0x100000000003a19381f900e7c554c66 0x100000000004b941967eb9abfaf1bec 0x1000000000032041e68aa04d8e28a22 0xf6c87fe353510042744 (Q 0x2413f5ea0cef0b33bd05 0x45c66e0dff6a64dd6259 0x5aa12c7d0fc91c1d8e23)) (M 0x10000000000041e20676348cc3e7b01 0x100000000001cada8ed86b900322c30 0x100000000000d80ab6eb74db31cdbbd 0x10000000000010786edcbb2ade2f50e 0x1000000000017c936875f92c1428c93 0x100000000002e72720a39434be2c3be 0x100000000002dbbbf76cbc150190fdf 0x100000000002aa170cc03fe9a48395f 0xd8ab391dfac07c8eda6 (Q 0x1cf8f392d715753b2640 0x342ef04f88a7e57702d6 0x3e85747de8ce1f02c344)) (M 0x1000000000001c0dd24ba7c57e23747 0x10000000000177e390429d130703be4 0x100000000000bb2283dab44f82d06b5 0x10000000000020607edf73bd6cf1840 0x100000000000ec967f8ed4ea3ae605e 0x1000000000024e1812aa7cb1f411317 0x100000000001bce46550b5109465bed 0x1000000000021f35bc39ce4ebb6ff99 0xbdea424869502b35017 (Q 0x178ef360cc19b015d7a9 0x27bc1604c1a114a220e8 0x2be24dba1d6ea42d8d2e)) (M 0x100000000000046dd1a9326f90868bb 0x10000000000135f1c3bd8668c3c5966 0x100000000000a0b93056588fc18456c 0x1000000000002aaa69143e9842dabbc 0x1000000000009475bff9bce9db7cc5f 0x100000000001d624b2282f753d84c8b 0x10000000000112f81efe7dcaf8c409d 0x100000000001a4567331b2e71c01304 0xa64a432c44899004dc7 (Q 0x135f9e1861141e701700 0x1ed06cd4bf1e7b4ea0ae 0x1f64965a87fa38a4edac))

private def cneg_bt_17 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffffc061fbd2b3694009d72b9) (L 0x1000000000c6793cbb9d7177c6aedff))) (N (L 0xffffffffe3a197369de9e0ba3a78cb) (N (L 0x100000000381c069d4abd14c3c6f7b1) (L 0xffffffffa0512a4b681fbaa3f12c7e)))) (N (N (L 0x100000000939244be9c32751d840421) (N (L 0xffffffff31282993d81f2e6a5b032e) (L 0x1000000010cd2220c4b332a23f5338e))) (N (L 0xfffffffeba653e195f4133957b286a) (N (L 0x1000000017366d2b7015a19f25b9d37) (L 0xfffffffe6f594de59cd3b0c6074d89))))) (N (N (N (L 0x1000000019b4d8d0924893e233c8c6a) (N (L 0xfffffffe6cd406cfd701f5950ad8f2) (L 0x1000000017ae97cffcafa551d2ef434))) (N (L 0xfffffffea9a872f79736319c9666d2) (N (L 0x1000000012a3631a3f12aa8357871f5) (L 0xffffffff050325c738798f85bf87a4)))) (N (N (L 0x100000000cc8c1e066ee2f6adbfce1b) (N (L 0xffffffff5e4e579df2b4c3f2ea43c5) (L 0x1000000007c3112e40c512e31dccf91))) (N (L 0xffffffffa3304101c51433cbe71bd3) (N (L 0x10000000043946043312adbed811999) (L 0xffffffffcffff0d567fcfa49da1b0b)))))) (N (N (N (N (L 0x100000000214b672216a430ea4c10c3) (N (L 0xffffffffe96cb5c3cb8e40317d01e0) (L 0x1000000000efa367ed54b8684e60e4f))) (N (L 0xfffffffff644ef806e77c6f5c995df) (N (L 0x100000000063229e69bc247045e936a) (L 0xfffffffffc217030f7419cbc6f15ff)))) (N (N (L 0x100000000025f2256b67036160f130f) (N (L 0xfffffffffe928bd21e4bb278e5c8ab) (L 0x10000000000d82a3dddfba208dd1918))) (N (L 0xffffffffff824920a9d9fb2afc2984) (N (L 0x1000000000047ebef60f207de84604a) (L 0xffffffffffd780c46c20ae295f19e7))))) (N (N (N (L 0x1000000000016740271b5adb0421aa4) (N (L 0xfffffffffff3bc8cf03c41d39a93ac) (L 0x100000000000699dcd9b7c14660e674))) (N (L 0xfffffffffffc7f3a9bc39f49afa813) (N (L 0x1000000000001d55c22a324228de9f8) (L 0xffffffffffff0da165af9dfe8a9301)))) (N (N (L 0x10000000000007b859a974c0a775743) (N (L 0xffffffffffffc1d98c8842345d9838) (L 0x10000000000001ee1cf50e2bdef58bf))) (N (L 0xfffffffffffff0d75fb37b804cb58b) (N (L 0x1000000000000075a377033abf74097) (L 0xfffffffffffffc79abb4e8b539770c))))))) (N (N (N (N (N (L 0x100000000000001aba8f6c7b57c025f) (N (L 0xffffffffffffff379056210564ab6b) (L 0x1000000000000005ceaf50ecdf5d10c))) (N (L 0xffffffffffffffd56283a49248dc09) (N (L 0x10000000000000013572556065b22e4) (L 0xfffffffffffffff7500257b86f3c19)))) (N (N (L 0x10000000000000003dcf221144f4cfb) (N (L 0xfffffffffffffffe4c94be2565b19e) (L 0x10000000000000000bdda632d067896))) (N (L 0xffffffffffffffffae019c41e43bed) (N (L 0x100000000000000002314b499b2a6c3) (L 0xfffffffffffffffff120db253806e8))))) (N (N (N (L 0x10000000000000000063f65c40aedb6) (N (L 0xfffffffffffffffffd6609f749c3ba) (L 0x100000000000000000112e0febe7764))) (N (L 0xffffffffffffffffff8f83b3100f98) (N (L 0x10000000000000000002da4a531e107) (L 0xffffffffffffffffffeda210aa9f60)))) (N (N (L 0x100000000000000000007549f4bc1e3) (N (L 0xfffffffffffffffffffd190799a5a5) (L 0x10000000000000000000123d1b9b3b8))) (N (L 0xffffffffffffffffffff8e4662ac29) (N (L 0x1000000000000000000002bfab529ca) (L 0xffffffffffffffffffffef1f0ab27e)))))) (N (N (N (N (L 0x100000000000000000000066df4c0c5) (N (L 0xfffffffffffffffffffffd91a10e42) (L 0x10000000000000000000000e99fd39a))) (N (L 0xffffffffffffffffffffffa8ee1793) (N (L 0x100000000000000000000002038a490) (L 0xfffffffffffffffffffffff428bf70)))) (N (N (L 0x1000000000000000000000004524920) (N (L 0xfffffffffffffffffffffffe6efcef) (L 0x1000000000000000000000000906347))) (N (L 0xffffffffffffffffffffffffcc5b02) (N (L 0x1000000000000000000000000125a02) (L 0xfffffffffffffffffffffffff98558))))) (N (N (N (L 0x10000000000000000000000000245dd) (N (L 0xffffffffffffffffffffffffff352a) (L 0x1000000000000000000000000004644))) (N (L 0xffffffffffffffffffffffffffe7cf) (N (L 0x1000000000000000000000000000846) (L 0xfffffffffffffffffffffffffffd30)))) (N (N (L 0x10000000000000000000000000000f2) (N (L 0xffffffffffffffffffffffffffffaf) (L 0x100000000000000000000000000001a))) (N (L 0xfffffffffffffffffffffffffffff8) (N (L 0x1000000000000000000000000000002) (zL)))))))

private def cneg_lf_17 : FastDTree := dleaf cneg_bt_17 0x100000000000a19fa36f9813b8211db 0x1000000000022735924a3dc51073144 0x100000000000ea6689768cf22cd7481 0xfffffffffffd78bd52009a45a5fb47 0x23e6a7f705a30b8db79f 0xeddda6f8bc35c02e5c5 (M 0x1000000000007a2308cbbed0949dfe9 0x100000000001ee3d50ce85fc7e6c81c 0x100000000000dcc6a12731c370ddc2a 0xfffffffffffe5f94255dc874d8899e 0x1000000000022aafe7a8cb7cf012dce 0x1000000000035cd18cb712861f464d7 0x10000000000468e1d0b6a30e46179ae 0x1000000000031d42e1814f2fa8571ec 0xde4e034f3f7507d6691 (Q 0x1fd1b74312d72ee0dc6b 0x4000dd1fee76f0d957ee 0x56607163c1ff3b90c2ee)) (M 0x10000000000043b7b6077a5661ba832 0x1000000000018e7b40a5b356854ec7e 0x100000000000c1d33b6d32f2041ef40 0xffffffffffffcd2192e2380a7dc1e9 0x1000000000014f37a011f561172272e 0x100000000002a4cf0085c5f203908b6 0x1000000000029a62649ca899360b3e5 0x1000000000029ad11687c09c5ce0fe8 0xc1d9ec39de0a444115c (Q 0x19431cb8479dfed6307c 0x2f34673dc6c26088e15a 0x3aeb736553d91e7025a0)) (M 0x100000000000229cdd3f245e4d56c8e 0x10000000000143877c5c879916a5d97 0x100000000000a8482a071ab2616f79b 0x1000000000000cef2bf3149e712f9d7 0x100000000000cdc622963fb52010a6b 0x10000000000210855b76ed808ea4e29 0x10000000000189a1853d2ad82eef9b0 0x1000000000020915d145e99982cc6c2 0xa8c73e38fec1e40e680 (Q 0x1456024d2882a4c329bd 0x2372a858164ebfb21d5e 0x28d0cfbcd80cd0b32e2d)) (M 0x1000000000000e1ae1acf1ab78bac31 0x10000000000108ea7f29cd80819d30d 0x10000000000090e0ae5ca4a08e947f7 0x10000000000017c15bbe2c45556cc10 0x10000000000080e31ab24bef12c662a 0x1000000000019e89e53bb6c01a74bdb 0x100000000000ebf4b82829c347582dd 0x1000000000018b3e497d751647b7220 0x92cff7699df9fbc40e1 (Q 0x1094a92a212112a42f4d 0x1b21cf962c1b273c7c86 0x1cc5160c9d55be99f78f))

private def cneg_bt_19 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffffbbab9cb2e6a074307ed00) (L 0x1000000000d9e7849234c10e9147757))) (N (L 0xffffffffdfcd117ab669c54c867969) (N (L 0x100000000410520e0cf8c76e638a2f4) (L 0xffffffff8e81c706433b28f7f76e45)))) (N (N (L 0x100000000b24f882e9d8c5d93115f7f) (N (L 0xffffffff014ba5bffea91ff9aff66a) (L 0x1000000015091351a94be1686103d77))) (N (L 0xfffffffe61972c51c45882306ec51c) (N (L 0x100000001dfe3686341d64f117ea7b9) (L 0xfffffffdf2a0a38b8014989eab7b83))))) (N (N (N (L 0x10000000222e33dcef4ff1409eb6d7c) (N (L 0xfffffffde09fa876ee480371179c47) (L 0x1000000020552e50883a1f58f717a13))) (N (L 0xfffffffe26b04676008766df8653d4) (N (L 0x100000001a153d3deb3d392df4d8376) (L 0xfffffffe9c95f2cbdb3e45d2f911f7)))) (N (N (L 0x10000000124fcdf6b1d8fb59597bc09) (N (L 0xffffffff15ca9b74f338d4b09d7827) (L 0x100000000b5dae6ff7d7142a4d33967))) (N (L 0xffffffff76a479b088bb9284bf751b) (N (L 0x100000000650f122079becd31b4e064) (L 0xffffffffb77ca9626898d204afbe23)))))) (N (N (N (N (L 0x10000000032ccd848c91032d3e8f3cf) (N (L 0xffffffffdd37a842e7342c06805c44) (L 0x100000000174c401eb6ff0c66f57584))) (N (L 0xfffffffff0b8847aa031550895759c) (N (L 0x10000000009d1aa6f21acb150e02631) (L 0xfffffffff9cfec7e10f76b7aad32ad)))) (N (N (L 0x10000000003d3992fefd5516a14cb8f) (N (L 0xfffffffffdad27f5a49092a1873df4) (L 0x1000000000162e5d1aba4c47f2568b3))) (N (L 0xffffffffff2fd77ccdc73355aa1b9c) (N (L 0x100000000007816e51823abcb118ce4) (L 0xffffffffffbbd213c60268cb98b93d))))) (N (N (N (L 0x10000000000261c3eb93d0e68461f01) (N (L 0xffffffffffeb045e72adc349aa2d9c) (L 0x100000000000b626060ffea77f8b400))) (N (L 0xfffffffffff9e942cd647da3046af6) (N (L 0x100000000000336275115ca349f8aaf) (L 0xfffffffffffe54338ee6c265693310)))) (N (N (L 0x1000000000000dbacbd35b432652336) (N (L 0xffffffffffff90a4ba220b25f37dd6) (L 0x100000000000037bddc696d5bf9b73a))) (N (L 0xffffffffffffe4704d980a39d224c1) (N (L 0x10000000000000d76f97712097688ea) (L 0xfffffffffffff97fb42054de1517b4))))))) (N (N (N (N (N (L 0x1000000000000031a61b2f3db40be1a) (N (L 0xfffffffffffffe891415b35650d6d3) (L 0x100000000000000af02f279c7736d81))) (N (L 0xffffffffffffffaf2eb09c45d6d17f) (N (L 0x10000000000000024ed81b1f229d89e) (L 0xffffffffffffffef4cfb5cb66f88e3)))) (N (N (L 0x1000000000000000779acdc38c77f8a) (N (L 0xfffffffffffffffcafdc1ddb14bce7) (L 0x10000000000000001743c19585c09be))) (N (L 0xffffffffffffffff5e31b9cfbf48f4) (N (L 0x1000000000000000045acabf5416261) (L 0xffffffffffffffffe2464647bc963f))))) (N (N (N (L 0x100000000000000000c9122ced4bd92) (N (L 0xfffffffffffffffffabc05b71a51da) (L 0x10000000000000000022fda6d99e5c2))) (N (L 0xffffffffffffffffff197b15995df5) (N (L 0x10000000000000000005e1c8a3c645b) (L 0xffffffffffffffffffd9e6102351fa)))) (N (N (L 0x10000000000000000000f4c7c4e4112) (N (L 0xfffffffffffffffffff9e821ada33e) (L 0x1000000000000000000026852a0eb88))) (N (L 0xffffffffffffffffffff0e64993766) (N (L 0x1000000000000000000005dfb4aa298) (L 0xffffffffffffffffffffdbb887fd13)))))) (N (N (N (N (L 0x1000000000000000000000de649a40a) (N (L 0xfffffffffffffffffffffab6ce05c9) (L 0x10000000000000000000001fedbd75b))) (N (L 0xffffffffffffffffffffff40870f4f) (N (L 0x1000000000000000000000047417401) (L 0xffffffffffffffffffffffe5ab0875)))) (N (N (L 0x1000000000000000000000009a9dc1f) (N (L 0xfffffffffffffffffffffffc7a4f28) (L 0x100000000000000000000000146719a))) (N (L 0xffffffffffffffffffffffff8a99d4) (N (L 0x100000000000000000000000029f181) (L 0xfffffffffffffffffffffffff11ca4))))) (N (N (N (L 0x1000000000000000000000000054037) (N (L 0xfffffffffffffffffffffffffe28e9) (L 0x100000000000000000000000000a410))) (N (L 0xffffffffffffffffffffffffffc738) (N (L 0x1000000000000000000000000001388) (L 0xfffffffffffffffffffffffffff954)))) (N (N (L 0x1000000000000000000000000000245) (N (L 0xffffffffffffffffffffffffffff3d) (L 0x1000000000000000000000000000041))) (N (L 0xffffffffffffffffffffffffffffec) (N (L 0x1000000000000000000000000000006) (L 0xffffffffffffffffffffffffffffff)))))))

private def cneg_lf_19 : FastDTree := dleaf cneg_bt_19 0x100000000000938b98da5b9ede508d4 0x100000000001e6401a92b9999009786 0x100000000000ced5bf779ebea1d1f1d 0xfffffffffffc9b1df50a244bbb4c68 0x1fc248774dacfc34f721 0xd5d8610f7fb1ee799c3 (M 0x100000000000703ead1cb2c7c203726 0x100000000001b106502dd02541472a8 0x100000000000c3019cf107fdc108dda 0xfffffffffffd7abc78ae9c4e2d4c7f 0x100000000001ec92d73f4838656b67a 0x10000000000320c64ea02eeb80c1c39 0x1000000000041d567b6cfbd6b7574ee 0x1000000000031cd9e547fe45725c4ee 0xc72205f8a7f39690768 (Q 0x1bf55f7845381f942d1b 0x3ac249dedcbd6c100e76 0x528cada783cb69bce7d5)) (M 0x100000000000407bad2f6542fdf6d59 0x10000000000158b223170e1910b4e53 0x100000000000ab74b5ccd63e381cfe9 0xfffffffffffedfbd903b6576ceacd7 0x10000000000122389ea7f7d3a3fd2df 0x1000000000026a7aa5f67203ddbf007 0x1000000000025cf51fffeda41cc4453 0x1000000000028e8339e23487455a162 0xac666132765ba2f6feb (Q 0x15eacf1931e61ba3a17e 0x2ab2ff0276c77284557d 0x37b44dfc1ab0d7ccc634)) (M 0x100000000000241d1f6bb22ef8e22f9 0x10000000000114cd4e861699db5c21b 0x10000000000095065490aead8f2f65e 0xffffffffffffdfa384f09e6e0b9be2 0x100000000000ae731a2f703b8873ae7 0x100000000001da31985b4566173d8b7 0x10000000000159710afcec9b6807526 0x100000000001f61ca469e87b0ee2bb3 0x9509dc147914fde34b0 (Q 0x11725e00524b16be603d 0x1f943c5107fb4e31d7de 0x26176c69ae10d5f4db2e)) (M 0x10000000000012d4ba6e9b102dfe0a2 0x100000000000e0a9f0c07f010637cc8 0x100000000000806c3c66363bac5c755 0x1000000000000901809d7beb505f06f 0x1000000000006c2234495c8d1e38665 0x1000000000016d62e719d243f13d505 0x100000000000c73fae56089ef9d3e6d 0x10000000000175529cef7cb3afa972a 0x80bcfdfbf741d760ed5 (Q 0xe173a2fb39cb708c95f 0x17d0d239e25b18f7676c 0x1a72aa6ed997715bdc9e))

private def cneg_bt_21 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffffb6f53d9319d7a85726746) (L 0x1000000000eeb91aaefb71c26a58a82))) (N (L 0xffffffffdb99b5d4a9056b99b112a0) (N (L 0x1000000004b1cd2e9a1ae7ce25fe601) (L 0xffffffff79e6acafe43a4a8ad65225)))) (N (N (L 0x100000000d6b2db4756564616747bb8) (N (L 0xfffffffec791aa6e154d139c5b2fdb) (L 0x100000001a3d266ad30f384add55d70))) (N (L 0xfffffffdf29ebf27fce071254115bf) (N (L 0x10000000269aea9b12f0083ec671f6e) (L 0xfffffffd51cc6790535bd7d3ef876e))))) (N (N (N (L 0x100000002d44fbc1df4545d562b49fe) (N (L 0xfffffffd2695e7e0ee58e2b86e730a) (L 0x100000002bf7a033618932eb7f0d397))) (N (L 0xfffffffd744106e8cf8d0e0eef39cc) (N (L 0x10000000245a97b47bcd4670fbb7a7b) (L 0xfffffffe0ac2a3284c73dac5ef8aaa)))) (N (N (L 0x100000001a1f45a92da6c9fc964ebd2) (N (L 0xfffffffeae261866fa85b1c563f237) (L 0x10000000109323a78e877e5fc7c0fd7))) (N (L 0xffffffff358e720ae3082af1cdd777) (N (L 0x100000000967f6067b984f3773abed3) (L 0xffffffff92e960445604df66bc48a4)))))) (N (N (N (N (L 0x1000000004d2fca5719376fa02d3dc0) (N (L 0xffffffffcaa22d6aa79dbf70b1c922) (L 0x1000000002416b1e2383975a17933a7))) (N (L 0xffffffffe81bfdf12d635143841367) (N (L 0x1000000000f7ebc6600da40ee369b96) (L 0xfffffffff6257e03a1bac3a6d58dda)))) (N (N (L 0x1000000000625df7f928abebe4e0941) (N (L 0xfffffffffc3be31917e930ccbf5877) (L 0x1000000000244313d79d3ca3b07259e))) (N (L 0xfffffffffea8cc46501749faa477d5) (N (L 0x10000000000c7a959fa6a916337448c) (L 0xffffffffff8db4ac2da64e02b785e9))))) (N (N (N (L 0x100000000004068afabeb76e312dcc5) (N (L 0xffffffffffdc407660e41a75280974) (L 0x10000000000138ca265649202424c85))) (N (L 0xfffffffffff5764aa43f77320c6dab) (N (L 0x100000000000599ed60d939a2687c23) (L 0xfffffffffffd1028fcabc029515647)))) (N (N (L 0x100000000000184fd7fef4745b428b2) (N (L 0xffffffffffff395739cab7bd7ac5b4) (L 0x1000000000000642d7ae457322898aa))) (N (L 0xffffffffffffce1afb3cd011301ad1) (N (L 0x1000000000000188d365facab6286be) (L 0xfffffffffffff40f9e2e1322adddc7))))))) (N (N (N (N (N (L 0x100000000000005bd28fa94b6fd5c48) (N (L 0xfffffffffffffd45bf863a4d8ba46c) (L 0x1000000000000014833735c0e032468))) (N (L 0xffffffffffffff6766ac0709fc770d) (N (L 0x100000000000000463368876f29512a) (L 0xffffffffffffffe00a4eae9f4784ca)))) (N (N (L 0x1000000000000000e66e8f510e7130a) (N (L 0xfffffffffffffff99327d133940f58) (L 0x10000000000000002d6a084d0e658c0))) (N (L 0xfffffffffffffffec2179a4ba73d8d) (N (L 0x1000000000000000089c652d28d7a49) (L 0xffffffffffffffffc4d86377f7a632))))) (N (N (N (L 0x10000000000000000192ac1c934be98) (N (L 0xfffffffffffffffff563885e89efde) (L 0x10000000000000000046f415d6a0693))) (N (L 0xfffffffffffffffffe29ab84c5a694) (N (L 0x1000000000000000000c131a80c0bd5) (L 0xffffffffffffffffffb14f1084465f)))) (N (N (L 0x10000000000000000001fc99f645b38) (N (L 0xfffffffffffffffffff3437f3dabc2) (L 0x1000000000000000000050fedfaa057))) (N (L 0xfffffffffffffffffffe00fa071e7e) (N (L 0x100000000000000000000c7f24bb92b) (L 0xffffffffffffffffffffb25dc77520)))))) (N (N (N (N (L 0x1000000000000000000001dea671d50) (N (L 0xfffffffffffffffffffff48ed3ed30) (L 0x10000000000000000000004582171c5))) (N (L 0xfffffffffffffffffffffe5cce4744) (N (L 0x100000000000000000000009ce12e4f) (L 0xffffffffffffffffffffffc5b3c98d)))) (N (N (L 0x10000000000000000000000158374ae) (N (L 0xfffffffffffffffffffffff81d8462) (L 0x1000000000000000000000002dec58a))) (N (L 0xfffffffffffffffffffffffef6500e) (N (L 0x10000000000000000000000005f6fe4) (L 0xffffffffffffffffffffffffddf0fd))))) (N (N (N (L 0x10000000000000000000000000c138c) (N (L 0xfffffffffffffffffffffffffbbec7) (L 0x1000000000000000000000000017d59))) (N (L 0xffffffffffffffffffffffffff7b51) (N (L 0x1000000000000000000000000002de2) (L 0xfffffffffffffffffffffffffff03c)))) (N (N (L 0x1000000000000000000000000000562) (N (L 0xfffffffffffffffffffffffffffe2c) (L 0x100000000000000000000000000009d))) (N (L 0xffffffffffffffffffffffffffffcc) (N (L 0x1000000000000000000000000000011) (L 0xfffffffffffffffffffffffffffffc)))))))

private def cneg_lf_21 : FastDTree := dleaf cneg_bt_21 0x100000000000821a3b6f7bb6c5e4e34 0x100000000001ad433f2723323e26cd9 0x100000000000b46447b04634790c2bb 0xfffffffffffc09985e2c77b789f600 0x1c08ba3a30838828ffec 0xbf35730cfdf70695aa2 (M 0x10000000000062d6056ec20ec59635c 0x1000000000017b472dced5a03c17f89 0x100000000000aa2e6f8dd7dbe59908e 0xfffffffffffcdffa11ed9375740480 0x100000000001b097d233b6d826a08c7 0x100000000002eca6c273f59e465e379 0x100000000003d67f614cb5de7f2e7de 0x1000000000031e8b181c6e1281954a7 0xb15ffd7de67b7ba7a0a (Q 0x187f1c766576be8d6143 0x360a5d635bbe8afdc0db 0x4f215f4d46937bdb23c9)) (M 0x1000000000003988c7001731d869346 0x100000000001296c737b83dedacb257 0x10000000000095b66fc7d2c63f3b8e8 0xfffffffffffe3839de51013ccfdf3c 0x100000000000f6499f3d6a03bcd95a0 0x100000000002377d482d645f0e4bef8 0x10000000000223650bacace9abac50a 0x10000000000284b7c843f04b86853eb 0x98660c8f7cca13eff09 (Q 0x12eeff8432c93e682662 0x26aa107f32d39c39f45c 0x34dc16541951a32fc163)) (M 0x10000000000021d2e46a983712c72e1 0x100000000000ebb61094e2da72e3f98 0x100000000000821f28c9b304e07ad92 0xffffffffffff31dc863c23df45251c 0x1000000000008f52867e819b1188c5f 0x100000000001aa8c743a02d04fbcb4f 0x1000000000012c5281db9aaf4fe9800 0x100000000001e5dc88467d6bf660520 0x82c20f73744cb07716d (Q 0xee202dac853660ff643 0x1c1fbc466bef7f1443d2 0x23b2ff2be955db3b7fdf)) (M 0x10000000000013c912c177dc712e6d3 0x100000000000bd418247756e26fd69b 0x10000000000070181d15877e03165ad 0xffffffffffffe1401999d2e911de85 0x10000000000056e6b7042fcd364ae76 0x1000000000014239ab0edcf4144fb68 0x100000000000a4e4bc3d43705b4976f 0x100000000001622f0121aa5f0a45341 0x701c58c7b48755c9c22 (Q 0xbe4991004861e7f8771 0x14dbce8028b4ef375b78 0x186afbff5fa84b123240))

private def cneg_sub_1 : FastDTree := (dsplit (dsplit cneg_lf_9 (dsplit cneg_lf_11 cneg_lf_13)) (dsplit (dsplit cneg_lf_15 cneg_lf_17) (dsplit cneg_lf_19 cneg_lf_21)))

private def cneg_node_2 : FastDTree := dsplit cneg_sub_0 cneg_sub_1

private def cneg_bt_25 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffffb23ede734d0edc7dce18d) (L 0x100000000104edff11f1839351e2779))) (N (L 0xffffffffd700f9edb0eae0fe103d5d) (N (L 0x100000000568001b87bf0de7fe28915) (L 0xffffffff6222871f97e347eb271e41)))) (N (N (L 0x100000001019c929f3b5b94b00b450a) (N (L 0xfffffffe822ff4cf0470b8dd3d0551) (L 0x10000000209bf6372ce29ffb8bcb236))) (N (L 0xfffffffd6876be72b1567268d61e6d) (N (L 0x10000000318073cf300c3e8ceb3dabb) (L 0xfffffffc83330c6bfb77d5396b25b4))))) (N (N (N (L 0x100000003bb94596befe71d88c60f2b) (N (L 0xfffffffc30b1762cfa3d7bacceedff) (L 0x100000003b8d8fb2e003faf25e8f2d0))) (N (L 0xfffffffc821d8f6e5542b70b6b4def) (N (L 0x10000000327798602077a41447c8bc8) (L 0xfffffffd3ff0d95960f7f9e3b24d98)))) (N (N (L 0x10000000251d1d6d761d3ec755b32fb) (N (L 0xfffffffe1a9dc9c882b575e0d659cb) (L 0x10000000181289b0c1e051afad68490))) (N (L 0xfffffffed6d91f11c6d064de505ffc) (N (L 0x100000000df34275ca2a73d856615b2) (L 0xffffffff5c9009c9169464eff2b0b8)))))) (N (N (N (N (L 0x10000000074cb8aaf00df4b2bca7d65) (N (L 0xffffffffae758f61981c9d49db19dc) (L 0x10000000037ab79cf2b503dc365c092))) (N (L 0xffffffffdaccc5985387e48cdc4c81) (N (L 0x1000000001859ac5506d3928e4d953f) (L 0xfffffffff05fe9aa10dbad39e58dfb)))) (N (N (L 0x10000000009d611cf53aeb109a88f94) (N (L 0xfffffffff9ebf1c17bc02f81eb06bd) (L 0x10000000003b0841c0b8457226689e5))) (N (L 0xfffffffffdcc879ba544248c06c8be) (N (L 0x100000000014a8e68448876ea40cab6) (L 0xffffffffff4135f95fddd30c6c0e63))))) (N (N (N (L 0x100000000006c64cd50458a0e4acc2e) (N (L 0xffffffffffc35aed1c4acdd0750cd2) (L 0x10000000000216d847327bddebd62e8))) (N (L 0xffffffffffedd6f809689afd348475) (N (L 0x1000000000009ba4215affba3bc2eaa) (L 0xfffffffffffadc50c2927d59dd503c)))) (N (N (L 0x1000000000002addbfbe42a982a12bb) (N (L 0xfffffffffffe9f1c970d3b591df1f1) (L 0x1000000000000b343c512744074f13c))) (N (L 0xffffffffffffa61029a3387057ee79) (N (L 0x10000000000002c932b1b36f6cfcb30) (L 0xffffffffffffea2b4d296a62158584))))))) (N (N (N (N (N (L 0x10000000000000a9168c05d71593cf1) (N (L 0xfffffffffffffaf130f146f467a204) (L 0x10000000000000264d1ede55380bb27))) (N (L 0xfffffffffffffee11c4170394cc8a8) (N (L 0x10000000000000084e0507098da99d5) (L 0xffffffffffffffc31969afe679878c)))) (N (N (L 0x1000000000000001ba0701551367b56) (N (L 0xfffffffffffffff397e95b1a5e94fe) (L 0x100000000000000058442d841984a6c))) (N (L 0xfffffffffffffffd921b6e3cfc7321) (N (L 0x100000000000000010f40247fa47ae4) (L 0xffffffffffffffff8acafbb1e93285))))) (N (N (N (L 0x10000000000000000322e40d768ba14) (N (L 0xffffffffffffffffeab59d8ab77cd1) (L 0x1000000000000000008f3fce4609e12))) (N (L 0xfffffffffffffffffc44936979924a) (N (L 0x10000000000000000018adbacf41777) (L 0xffffffffffffffffff5e307b4f522a)))) (N (N (L 0x100000000000000000041c232255f5d) (N (L 0xffffffffffffffffffe57ea089e2ce) (L 0x10000000000000000000a98f9a15b11))) (N (L 0xfffffffffffffffffffbcbe09478e3) (N (L 0x100000000000000000001a784f6967e) (L 0xffffffffffffffffffff5a9a19d35e)))))) (N (N (N (N (L 0x100000000000000000000401a7e51b2) (N (L 0xffffffffffffffffffffe7574f608a) (L 0x100000000000000000000096a6e65b3))) (N (L 0xfffffffffffffffffffffc6e4adfb4) (N (L 0x1000000000000000000000157deece2) (L 0xffffffffffffffffffffff7f80222d)))) (N (N (L 0x100000000000000000000002faeeecf) (N (L 0xffffffffffffffffffffffee6d7725) (L 0x10000000000000000000000066e8bda))) (N (L 0xfffffffffffffffffffffffda9608d) (N (L 0x1000000000000000000000000d831ff) (L 0xffffffffffffffffffffffffb26e4d))))) (N (N (N (L 0x10000000000000000000000001ba6c0) (N (L 0xfffffffffffffffffffffffff634b7) (L 0x100000000000000000000000003727a))) (N (L 0xfffffffffffffffffffffffffecb56) (N (L 0x1000000000000000000000000006b4b) (L 0xffffffffffffffffffffffffffdaef)))) (N (N (L 0x1000000000000000000000000000cba) (N (L 0xfffffffffffffffffffffffffffba9) (L 0x1000000000000000000000000000178))) (N (L 0xffffffffffffffffffffffffffff82) (N (L 0x100000000000000000000000000002a) (L 0xfffffffffffffffffffffffffffff3)))))))

private def cneg_lf_25 : FastDTree := dleaf cneg_bt_25 0x1000000000006e9a9d8d1f65daa2113 0x1000000000017bd15ea42622a77d959 0x1000000000009bb49725eec41b43a55 0xfffffffffffbb9f83289cd07567d87 0x18b981dfb700f8dc76da 0xaa0ec3361a346803517 (M 0x100000000000532fcac0cfa8b4254f5 0x1000000000014c9fc5cdcf398716fc1 0x10000000000092ef1d1f2c68a8b09ae 0xfffffffffffc859559f02d27ee9267 0x10000000000177473d89b2fc8450562 0x100000000002bfa22bd2ed87a517563 0x10000000000394328e90b3359733965 0x10000000000321e5440799ad44f0f3c 0x9d1eb41d58c7dba5cdb (Q 0x156de5c735d43081743a 0x31d7467288113a9e9602 0x4c18f9749700350cfae8)) (M 0x10000000000030141eede787391f1a5 0x100000000001006265f6ba483780988 0x1000000000008138b24658acff10cb1 0xfffffffffffdcdcd12f0d20be8fa51 0x100000000000cbfb63ee8e7d02708a8 0x1000000000020b21f27b1f9729725ce 0x100000000001ed98d7d3165b68ea23a 0x1000000000027d021771a54775927d2 0x85e9e08f1733ff4ec27 (Q 0x104da7d0801aaaa16a93 0x2317eae77057c49b6d68 0x325dd4fb21a77d8c6412)) (M 0x1000000000001ce0de2db00c74a022d 0x100000000000c80eeaa53afd1e2375f 0x1000000000007030359d2d3aad31901 0xfffffffffffebdb2afe799c34a3426 0x10000000000070f9a3910a2400f65a1 0x10000000000180fb5f6ba6a931e68b6 0x100000000001023b098efdb44d88e1b 0x100000000001d7ef436447ab2c1fa9d 0x71fb8532a5a7ceea5f7 (Q 0xca21c3602d0dd451ed4 0x1913760273bd323db459 0x219f6d28cfebe14c4a13)) (M 0x1000000000001207da8d31862f207b5 0x1000000000009e901eeb47d1ce9268a 0x100000000000607e4f91394f9d296d8 0xffffffffffff6870d675510c1d6d71 0x10000000000041c705c60faab0fbf8f 0x1000000000011c8c3cb6a921bf4dbb3 0x10000000000084e52a75caffd0a570d 0x1000000000015175031ea082c36f60a 0x60f511359592aaed231 (Q 0x9f95bc8c770d6f7ea05 0x1240d38bf290edcc5197 0x16aaeac9a6851e0233da))

private def cneg_bt_27 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffffad887f53804610a475bd4) (L 0x10000000011c8631bb16f68147e4e40))) (N (L 0xffffffffd1fc536f094832d5f9f278) (N (L 0x100000000634d7f7047b792fa1c0ca6) (L 0xffffffff46cf36f518b6d900f545b5)))) (N (N (L 0x1000000013409c7936b2bd6152ae5da) (N (L 0xfffffffe2f1603aeadb5f7c1900f8c) (L 0x1000000028612f30f0b8b1e6cd494ba))) (N (L 0xfffffffcbd169da2e99fea2bf9bfac) (N (L 0x100000003f3cb73ca0bf865be7ab52f) (L 0xfffffffb7acd70a6b05ed5023d29d7))))) (N (N (N (L 0x100000004e7e11997e503dc7b2eaa8e) (N (L 0xfffffffaecf0405a5d0f9b5e13701d) (L 0x100000005059b837d7aeb3b39b44fcc))) (N (L 0xfffffffb3ad035fa1dd9ee93c60b00) (N (L 0x1000000045c8ad7b222b8fa2c662a2d) (L 0xfffffffc26f7f07dbbe8d29374ab28)))) (N (N (L 0x1000000034854002294e9e100b0f97f) (N (L 0xfffffffd4972c4e481d05de5098007) (L 0x1000000022d23c49c48c05cc86e7359))) (N (L 0xfffffffe4d97a3221f0dd0c1aff828) (N (L 0x10000000149b1b253ab34569f284dcc) (L 0xffffffff0c21b893207a8c194800cc)))))) (N (N (N (N (L 0x100000000b001feb9bc289b3fb44afe) (N (L 0xffffffff83eba08920bb47a6faef9c) (L 0x1000000005585e381ace2bba4287f4d))) (N (L 0xffffffffc6506eef91685e9c042e56) (N (L 0x100000000261bb3742a9e650d282091) (L 0xffffffffe753145a4331b3f72384fa)))) (N (N (L 0x1000000000fabfe82b29073160f05af) (N (L 0xfffffffff63b0199501c3205d7436f) (L 0x10000000005fb3410df79099f470d14))) (N (L 0xfffffffffc66c1aba2d53fe2a74161) (N (L 0x1000000000220f9147c8e7c4a204922) (L 0xfffffffffec2dadc786b63de5361de))))) (N (N (N (L 0x10000000000b5a63e7a58526a6c039c) (N (L 0xffffffffff998d6ee29659270f41e1) (L 0x1000000000038eaf60d7a75a073054e))) (N (L 0xffffffffffe0d60a8e546d5e940b27) (N (L 0x1000000000010d27613a00e6e9997fd) (L 0xfffffffffff70b5e5f584c61591c4a)))) (N (N (L 0x1000000000004b4294c2ee26f7d04f3) (N (L 0xfffffffffffd8fcf887a1e83c06114) (L 0x10000000000013f6c693cf607a007ad))) (N (L 0xffffffffffff5e93855f9344bd9771) (N (L 0x100000000000050953ef83d66c622fa) (L 0xffffffffffffd84087d20f9894ee1c))))))) (N (N (N (N (N (L 0x100000000000013609ca1e9276b58aa) (N (L 0xfffffffffffff6a93e3ad0f51a24c8) (L 0x100000000000004735b951d0715529d))) (N (L 0xfffffffffffffde6f4a55b1bc87276) (N (L 0x100000000000000fa6d7de268cf5ba3) (L 0xffffffffffffff8c733650d238a40c)))) (N (N (L 0x10000000000000034c455506fbe6981) (N (L 0xffffffffffffffe8259c588752851a) (L 0x1000000000000000aad01d547a97713))) (N (L 0xfffffffffffffffb44b416ff971f23) (N (L 0x1000000000000000213bab33c1cae0d) (L 0xffffffffffffffff18c65066636577))))) (N (N (N (L 0x10000000000000000639f50d3cfa202) (N (L 0xffffffffffffffffd5779c61ad0ef9) (L 0x1000000000000000011ff442b19f79e))) (N (L 0xfffffffffffffffff87395b1f3eaaa) (N (L 0x100000000000000000323859d7d0114) (L 0xfffffffffffffffffeb4b8335d38e5)))) (N (N (L 0x1000000000000000000877129f1de08) (N (L 0xffffffffffffffffffc914921881a5) (L 0x10000000000000000001616c0e74be1))) (N (L 0xfffffffffffffffffff72fc2f27f28) (N (L 0x1000000000000000000037d2b445002) (L 0xfffffffffffffffffffea128c1e8f1)))))) (N (N (N (N (L 0x10000000000000000000088c2e6d32c) (N (L 0xffffffffffffffffffffcb16f02cd3) (L 0x1000000000000000000001451828f57))) (N (L 0xfffffffffffffffffffff84121f529) (N (L 0x10000000000000000000002ee714d0b) (L 0xfffffffffffffffffffffee600ef40)))) (N (N (L 0x1000000000000000000000069393ec4) (N (L 0xffffffffffffffffffffffd9023df9) (L 0x100000000000000000000000e598966))) (N (L 0xfffffffffffffffffffffffac1297d) (N (L 0x1000000000000000000000001e79922) (L 0xffffffffffffffffffffffff501ca9))))) (N (N (N (L 0x10000000000000000000000003f08f6) (N (L 0xffffffffffffffffffffffffe98de7) (L 0x100000000000000000000000007f120))) (N (L 0xfffffffffffffffffffffffffd3521) (N (L 0x100000000000000000000000000f9cc) (L 0xffffffffffffffffffffffffffa93f)))) (N (N (L 0x1000000000000000000000000001df1) (N (L 0xfffffffffffffffffffffffffff5ba) (L 0x1000000000000000000000000000380))) (N (L 0xfffffffffffffffffffffffffffed1) (N (L 0x1000000000000000000000000000065) (L 0xffffffffffffffffffffffffffffdf)))))))

private def cneg_lf_27 : FastDTree := dleaf cneg_bt_27 0x1000000000005a2942083709e643912 0x10000000000151538c3aaeb34b93d6e 0x100000000000853c8b7ccc1864c1c2e 0xfffffffffffba118aabf5e7fb8b436 0x15d2aebd2bd6c673d813 0x9679532cea6bada4f6c (M 0x1000000000004262609f9077a12c18a 0x10000000000124869e424a287e0b67b 0x1000000000007dba35bf5c19c519cb3 0xfffffffffffc60de47fd0e7c6629a1 0x1000000000014106597e76e915f420c 0x10000000000298e7c1c7510b9223fdf 0x100000000003563e259ed137ab8b1b9 0x1000000000032682555d7f8c49f19f0 0x8a7026baf94bcc2f90b (Q 0x12bf6bcb9ab17a8e7181 0x2e258cc991f4a939a724 0x496d05ff96285fd9e440)) (M 0x1000000000002526bf1146446d75575 0x100000000000dd2304c480a89382881 0x1000000000006e72913641d4e821905 0xfffffffffffd96a791bd2807afd962 0x100000000000a3bd9874d1e0b9bf369 0x100000000001e4b10ae54fbff4757d0 0x100000000001bb6eb52c3f36bb32893 0x10000000000276ff217aee52a2844fe 0x74fe41bdd914a0b4ad6 (Q 0xe03c63656137f5db890 0x1ff9a34ff01c85e93c01 0x30339cbf33aa8e0a0966)) (M 0x1000000000001641ad8afba50354f24 0x100000000000a97c5431426a76cdb0e 0x1000000000005fb006d1be6634fc770 0xfffffffffffe7a29dbf395aead3ff7 0x10000000000053dec3b9e6c7c62cd3e 0x1000000000015cdeeabdad4fa29dd5f 0x100000000000db16e4ea5e2f6a64b02 0x100000000001cbf6cc40afcab0728f9 0x62bdaebf8c0534075b3 (Q 0xaaf0da0f7579db704a5 0x166cf85da41b2bda3615 0x1fd7a350c9982d576b7d)) (M 0x1000000000000e7caa182ba70dcd207 0x100000000000844cbc06dfbe1be7c5a 0x1000000000005213f15926b46a59d11 0xffffffffffff1d73e007463fa3b06e 0x1000000000002d3cd74e24699ed2757 0x100000000000fbd1e902cfe9ee36e17 0x100000000000673939a34fd5a000ab4 0x10000000000142ccfc3e3a2d156c9b3 0x534a5234cf6ded95433 (Q 0x851732b8157999cd153 0xffd9e065fcb3e1c3cce 0x152e73fba3c896d150d4))

private def cneg_bt_29 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffffa8d22033b37d44cb1d61a) (L 0x10000000013581b2aa6bca8c4c5fed9))) (N (L 0xffffffffcc853801ed4b6e7dc42ac8) (N (L 0x10000000071a60b561cfcd1001da92c) (L 0xffffffff277d405b2aa9b9a828df73)))) (N (N (L 0x1000000016f1704b4dc51e682795b68) (N (L 0xfffffffdcbe43a9b64f9de0033451e) (L 0x1000000031d2ef185fdf14f74353b04))) (N (L 0xfffffffbe944931261968e2be314d2) (N (L 0x10000000507cc4637cc0a36c0e1dec4) (L 0xfffffffa29b08ec3743c6013b3b2b3))))) (N (N (N (L 0x1000000066c5a3c621f489afd337c54) (N (L 0xfffffff944475e0b380f9d77a4f48e) (L 0x100000006bff1961f2ecc9adc3545fa))) (N (L 0xfffffff98218f6375e54608c943559) (N (L 0x10000000601eb373bf7dbabb611aa99) (L 0xfffffffaa33f8b366f2663ea23ea88)))) (N (N (L 0x100000004a07fbd08d22d2465d9b270) (N (L 0xfffffffc2210e7aba7a45c4c0384c6) (L 0x10000000322b799a1bfbabff59dcb41))) (N (L 0xfffffffd8777d31cfcb2b0d569e49b) (N (L 0x100000001e50ad63cad7acebfe4b4a0) (L 0xfffffffe9594bb232199989680885f)))))) (N (N (N (N (L 0x100000001082ba9bb4f2e1cbf7187b6) (N (L 0xffffffff43f42660e7fa932f5e0c04) (L 0x10000000082da057b1f4fb9cfe531f9))) (N (L 0xffffffffa6e95bdb793c8dc15db57f) (N (L 0x1000000003b654fd831fd98540d4c14) (L 0xffffffffd93135687017934c839aa6)))) (N (N (L 0x10000000018ddfbc0fa6a74e15131e9) (N (L 0xfffffffff05ccab26c982071249010) (L 0x10000000009a8110af7604aab8a7a9b))) (N (L 0xfffffffffa240c3cdd4c511788ef8d) (N (L 0x100000000037ebf28c1b2c084b5b015) (L 0xfffffffffdf301a377bcbf7e0f256e))))) (N (N (N (L 0x100000000012f255aaf243f977f474b) (N (L 0xffffffffff53a82cc7896298e09ac9) (L 0x1000000000060826ae71afe9c092e40))) (N (L 0xffffffffffcabec31a5f6bc4829f67) (N (L 0x100000000001cf8078a6d3a600606ca) (L 0xfffffffffff075c8afb91c5118cec9)))) (N (N (L 0x1000000000008393f35352f7c416125) (N (L 0xfffffffffffbb49602afd6267f87c2) (L 0x100000000000236c37c476a72180051))) (N (L 0xfffffffffffedf7e00de4b7c9bd3c9) (N (L 0x1000000000000910ff1a0adfc3a40c7) (L 0xffffffffffffb7efd14740de1d9ed0))))))) (N (N (N (N (N (L 0x10000000000002361208ba979eb62c9) (N (L 0xffffffffffffeed46c9f5d64f84ff7) (L 0x1000000000000083d494cca2e22ac91))) (N (L 0xfffffffffffffc16f5b6ceccd2afd5) (N (L 0x100000000000001d5f5e13ad058b803) (L 0xffffffffffffff25b28c2461a78ece)))) (N (N (L 0x100000000000000645a978fee5ec922) (N (L 0xffffffffffffffd25602cff92371ec) (L 0x100000000000000149242998425ac5f))) (N (L 0xfffffffffffffff6d2cdd372acf68f) (N (L 0x100000000000000040dde7a356c2dc5) (L 0xfffffffffffffffe39cccbed81aef5))))) (N (N (N (L 0x10000000000000000c4ed50ef599565) (N (L 0xffffffffffffffffab65937f4083a6) (L 0x100000000000000002405740062d3c5))) (N (L 0xfffffffffffffffff0cc66a0a6785d) (N (L 0x10000000000000000065c14eeea4293) (L 0xfffffffffffffffffd5caff7ae6784)))) (N (N (L 0x100000000000000000115c325f9d81c) (N (L 0xffffffffffffffffff8eb2999f02ee) (L 0x10000000000000000002dd76212aae7))) (N (L 0xffffffffffffffffffed99fba0d92b) (N (L 0x1000000000000000000075374b96825) (L 0xfffffffffffffffffffd1b076425d1)))))) (N (N (N (N (L 0x100000000000000000001228189f039) (N (L 0xffffffffffffffffffff8ef6cfb845) (L 0x1000000000000000000002ba79ecbb7))) (N (L 0xffffffffffffffffffffef43a2d38f) (N (L 0x100000000000000000000065e96e3e4) (L 0xfffffffffffffffffffffd97d88b21)))) (N (N (L 0x10000000000000000000000e72fbb95) (N (L 0xffffffffffffffffffffffa9dc2eff) (L 0x100000000000000000000001fe0176d))) (N (L 0xfffffffffffffffffffffff448e2d0) (N (L 0x100000000000000000000000446e752) (L 0xfffffffffffffffffffffffe72eaf3))))) (N (N (N (L 0x10000000000000000000000008f1169) (N (L 0xffffffffffffffffffffffffccc8f7) (L 0x1000000000000000000000000123790))) (N (L 0xfffffffffffffffffffffffff98f9e) (N (L 0x1000000000000000000000000024304) (L 0xffffffffffffffffffffffffff35de)))) (N (N (L 0x1000000000000000000000000004622) (N (L 0xffffffffffffffffffffffffffe7d0) (L 0x100000000000000000000000000084a))) (N (L 0xfffffffffffffffffffffffffffd2d) (N (L 0x10000000000000000000000000000f4) (L 0xffffffffffffffffffffffffffffaf)))))))

private def cneg_lf_29 : FastDTree := dleaf cneg_bt_29 0x10000000000045ad37e2252f63e5bfd 0x1000000000012d16a8a346051298928 0x10000000000071460d4709ca9bbdddb 0xfffffffffffbb38974ad6f1cec6c7a 0x1350ba176a95499f6dee 0x84850df18e16aef7703 (M 0x1000000000003150c53ee7f0ed77a29 0x1000000000010255b04d14b1f6589cb 0x1000000000006adb4ed251af2a8b5ad 0xfffffffffffc66cee4f13f05c42773 0x1000000000010e19de689772406db84 0x10000000000277abaa07d3f6c19cba3 0x1000000000031c6a28ddc04c2bcd001 0x1000000000032c0792757b02e12a2b5 0x79615ecdf6ba19636d2 (Q 0x106fff1b68ae69ecfbfc 0x2aefec49c11bee5d1f04 0x471654142b32487e3fb3)) (M 0x100000000000199a43a6485f56ce2bb 0x100000000000bf205aee722ab564a88 0x1000000000005db21845c2cb08fc8c0 0xfffffffffffd88913edf6e8a31be00 0x1000000000007de10014332dc2e2e1d 0x100000000001c3753aec97020d5fe39 0x1000000000018cbe025075c3f063396 0x1000000000027255e014869fde7b7eb 0x65aaf6bced92de8353e (Q 0xc0d569df63eedc78904 0x1d4adc6e51a936364423 0x2e56b005e6c84fb5833b)) (M 0x1000000000000ec4468bbbd9462c3c1 0x1000000000008f85a345c5a48e03f4e 0x10000000000050ee0c39b3116f43934 0xfffffffffffe5dcda23448e6089f7e 0x100000000000385b15f0d46cd1c9568 0x1000000000013d979572d03bf5a8ea7 0x100000000000b6cb08b091206fc3f53 0x100000000001c19dc34bd9149b5289c 0x550bc43de1841160ba3 (Q 0x90479d9540ea1d91d44 0x1428db420724171a05ef 0x1e55a899c0ad0b9e5bce)) (M 0x10000000000009eaf39bd9d66973066 0x1000000000006e1150a4279e8f2f21a 0x1000000000004528e6bcfa6c9e48e30 0xfffffffffffef78d702d774f266f83 0x10000000000019a69cd7435b07b9761 0x100000000000df7fea6a73ef62d9dfc 0x1000000000004bd1917964b32ad9133 0x10000000000135e6a5dcd47c0e6a958 0x471b7c9fd9ed8958588 (Q 0x6e837d07e23d7d89145 0xe0f7859fe06f262c497 0x13f0a7b0968c322142a0))

private def cneg_bt_31 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffffa41bc113e6b478f1c5061) (L 0x10000000014fe081dfefffb45f5393f))) (N (L 0xffffffffc6951d4f9822a151c4df3c) (N (L 0x10000000081ac51d142510eb4ae4ef9) (L 0xffffffff03b339ca36de1e4af11d20)))) (N (N (L 0x100000001b4031cfc5e6e8d23eca3df) (N (L 0xfffffffd55e2352c3a6ae0467c3da0) (L 0x100000003d43503305de52de8cccbb0))) (N (L 0xfffffffae460d121c6f390c50d8b66) (N (L 0x100000006612ed100bd4d99e29dcd73) (L 0xfffffff87d6ca625de452d9d4ec707))))) (N (N (N (L 0x1000000086109230d0b15d2f34b31cc) (N (L 0xfffffff71956a0c753363d47696631) (L 0x10000000909ba3f68f2d717ad1855a0))) (N (L 0xfffffff732eb58e287d56e6fee39bb) (N (L 0x1000000083e37eb4046b21540477f66) (L 0xfffffff88e48886051e13c32b96f3f)))) (N (N (L 0x1000000067f29950784b209e7d36a2b) (N (L 0xfffffffa828f4c8f056a565bdbc564) (L 0x1000000048002d12558732b3433590e))) (N (L 0xfffffffc6a9bccff0f70d5efd16349) (N (L 0x100000002c6c4762e9f9d88dfea8f7a) (L 0xfffffffde789cda756944e614276cc)))))) (N (N (N (N (L 0x1000000018ae9e2554f6c52ea44132c) (N (L 0xfffffffee42693bf9858a69688255d) (L 0x100000000c766b8bd5fbe37fa1b264d))) (N (L 0xffffffff76f7f1269a954d3659292b) (N (L 0x1000000005c335375589f5139ee70c9) (L 0xffffffffc336a1701d683136350e71)))) (N (N (L 0x100000000274c142f0ab6f01e1df64a) (N (L 0xffffffffe712664e4bd5af328c53fc) (L 0x1000000000f86bd5d0607d7d9ab7c93))) (N (L 0xfffffffff67fcfb773e7dae3d1eb97) (N (L 0x10000000005b6fa706f588ccd1c9a5c) (L 0xfffffffffc9e8451a460f78c9c05ad))))) (N (N (N (L 0x10000000001f7d18cef65a56b00a0ea) (N (L 0xfffffffffedf45f174153c1180207c) (L 0x10000000000a2f67fa12272b54a2f60))) (N (L 0xffffffffffa55f5a9ba2065bc5f5ac) (N (L 0x1000000000031add32c714faa66b0f4) (L 0xffffffffffe525ae004b4f531813cc)))) (N (N (L 0x100000000000e51442e4f6bed10116a) (N (L 0xfffffffffff877a4bdcd6909d30c8c) (L 0x1000000000003e96af0aa3ddd3e2dbe))) (N (L 0xfffffffffffdfe85437f02b876391d) (N (L 0x10000000000010409f20d7da6f068b5) (L 0xffffffffffff7de5fbf76f1a5a213a))))))) (N (N (N (N (N (L 0x10000000000004052f23ed68b19c9a7) (N (L 0xffffffffffffe0907ffaac022ea641) (L 0x10000000000000f306c18b8b2cc79ae))) (N (L 0xfffffffffffff8bdf81060dde7dab5) (N (L 0x1000000000000036e359b06e3301c08) (L 0xfffffffffffffe6551f4fbc9b7de19)))) (N (N (L 0x100000000000000be0be76d5c027bcb) (N (L 0xffffffffffffffa8f3e7eb7cac1507) (L 0x10000000000000027787566b41534b1))) (N (L 0xffffffffffffffee4759c03abd9330) (N (L 0x10000000000000007e12842a3b5d879) (L 0xfffffffffffffffc879ceff1318672))))) (N (N (N (L 0x10000000000000001839c3fac865d12) (N (L 0xffffffffffffffff586eba344785b7) (L 0x1000000000000000047c9c9db71cd02))) (N (L 0xffffffffffffffffe18474fbd21daf) (N (L 0x100000000000000000cd4a65ef12776) (L 0xfffffffffffffffffaa5496210d0bd)))) (N (N (L 0x1000000000000000002372f2d5b532a) (N (L 0xffffffffffffffffff1741637d648a) (L 0x10000000000000000005eb9d6252d67))) (N (L 0xffffffffffffffffffd9c1eaad806a) (N (L 0x10000000000000000000f5112e8cec0) (L 0xfffffffffffffffffff9e9d3736f01)))))) (N (N (N (N (L 0x100000000000000000002666cd37669) (N (L 0xffffffffffffffffffff0f8e902e08) (L 0x1000000000000000000005d6370d3af))) (N (L 0xffffffffffffffffffffdbfed7feb6) (N (L 0x1000000000000000000000dc7ac5458) (L 0xfffffffffffffffffffffac38ce312)))) (N (N (L 0x10000000000000000000001f9bceb39) (N (L 0xffffffffffffffffffffff42861d13) (L 0x10000000000000000000000467f816a))) (N (L 0xffffffffffffffffffffffe5f2d116) (N (L 0x10000000000000000000000098fedc7) (L 0xfffffffffffffffffffffffc837332))))) (N (N (N (L 0x1000000000000000000000001434da1) (N (L 0xffffffffffffffffffffffff8ba665) (L 0x1000000000000000000000000299aa5))) (N (L 0xfffffffffffffffffffffffff137a4) (N (L 0x1000000000000000000000000053840) (L 0xfffffffffffffffffffffffffe2b16)))) (N (N (L 0x100000000000000000000000000a38c) (N (L 0xffffffffffffffffffffffffffc74e) (L 0x1000000000000000000000000001389))) (N (L 0xfffffffffffffffffffffffffff950) (N (L 0x1000000000000000000000000000246) (L 0xffffffffffffffffffffffffffff3b)))))))

private def cneg_lf_31 : FastDTree := dleaf cneg_bt_31 0x10000000000031d81f76be7251213d1 0x1000000000010e57f6723144269bc7a 0x1000000000005ff1e4ef74884edcf85 0xfffffffffffbe624e62248db13c7aa 0x112e66dda883466f1cd8 0x743c850689ef40a48b5 (M 0x10000000000020aa614fbb73a33ce9b 0x100000000000e556b93bbf60de2d10a 0x1000000000005a75ab010f58438c3da 0xfffffffffffc8c9fbbe142532094f2 0x100000000000dea936b21fbe13ebbde 0x1000000000025b2b2d0072948655ea4 0x100000000002e67a2fc044c87c663cb 0x1000000000033225925aafd6b41efbd 0x69fa39ed7759a25dfa6 (Q 0xe7a74b014366b626aa1 0x282f457d7a1753fb6c18 0x450d308aa515948175f1)) (M 0x1000000000000e184a59debe4ae22fb 0x100000000000a5bb3efbddc40773baf 0x1000000000004f1e9de69b1afbd7d66 0xfffffffffffd997a4c8df891fb27a0 0x1000000000005a9a451eb555a2bf696 0x100000000001a6bfa13360bfc6bfa78 0x1000000000016158e9eaf7ac7843738 0x1000000000026eb76836fe2fd324716 0x57f3028b57789b4ae44 (Q 0xa6546c3b610584a7c2b 0x1b059381faba111300a2 0x2cbfb636f9aa24094884)) (M 0x100000000000070b0c210e1929cfd4f 0x10000000000079a0519875f3a1decb5 0x10000000000044149e307c80ef49ca0 0xfffffffffffe5f3e613aaa251040fb 0x1000000000001ead10e60805ba1c121 0x1000000000012289f3dd856a7cc156c 0x1000000000009536a087b3ace9c6c29 0x100000000001b897aeea1150b7a1995 0x48e4ae935fd60d492dd (Q 0x79d47f441eec1ef9603 0x12427659a5fc6126fb41 0x1d12c706a48ed9e0b84d)) (M 0x10000000000004ecd7873fa1cf4fc69 0x1000000000005b6596d59f26a04992c 0x10000000000039e997222226403d094 0xfffffffffffeee0586ba99212e2b82 0x10000000000007498f45d1ccb28c6fc 0x100000000000c70d7cf1229f07fd81c 0x1000000000003298aabb146c2953980 0x1000000000012a797137028183be9ce 0x3c641d748f92c740d59 (Q 0x5b878d8d67759f33813 0xc72fa45929d3b985ce0 0x12ebb87d2d294b95bc97))

private def cneg_sub_3 : FastDTree := (dsplit (dsplit cneg_lf_25 cneg_lf_27) (dsplit cneg_lf_29 cneg_lf_31))

private def cneg_bt_34 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff9f6561f419ebad186caa7) (L 0x10000000016ba29f5ba395f980bfd78))) (N (L 0xffffffffc025790144fbd8ae5208a0) (N (L 0x1000000009384ec6b2cdb01ae4aa6ac) (L 0xfffffffedaed3acae75d287c2ec0c0)))) (N (N (L 0x10000000204322dc56e368a0a6f87b4) (N (L 0xfffffffcc9f43dcccd0d2ed1350147) (L 0x100000004b122424d16264ed5b87c47))) (N (L 0xfffffff9a4290a37e31e82b2c99e3c) (N (L 0x1000000080fde7c6757630eb222d75e) (L 0xfffffff65f4d4766b24c7aeee7114e))))) (N (N (N (L 0x10000000ae4010b1f5f0618ee53ab42) (N (L 0xfffffff446cdc78da3e57b4c07009e) (L 0x10000000c0e9b808c8b8a7b7fc5d054))) (N (L 0xfffffff41cdf276258c366c52c3a57) (N (L 0x10000000b4491c2083326f00f923c22) (L 0xfffffff5b4718fdf84fc6810ce847f)))) (N (N (L 0x1000000091654a1c42314bb70e9bd8d) (N (L 0xfffffff83c53737ebdcf78bc62a24c) (L 0x1000000066ee70d49c316a756c19122))) (N (L 0xfffffffad2a2c02f9c28b386553591) (N (L 0x1000000040d784e5b0a40a7135735ac) (L 0xfffffffce9083a5432474955eda785)))))) (N (N (N (N (L 0x1000000024c098a617d318c08b2dadf) (N (L 0xfffffffe553c17217ef5a7a9455a15) (L 0x1000000012ea7bf11ea10fc5701deae))) (N (L 0xffffffff2e10a6dfc104bde52a1adb) (N (L 0x1000000008e8d17230215c5a775f8bb) (L 0xffffffffa12b3bc1b752856cd765d1)))) (N (N (L 0x1000000003dd9d3cf5fac0b07c06db2) (N (L 0xffffffffd86c0397fbc70ae617bbc2) (L 0x10000000018dcf6a05557684d9d5d29))) (N (L 0xfffffffff0a82f2878c8a0f6004dbf) (N (L 0x100000000094e591a249f3d147ba48c) (L 0xfffffffffa7304adf9f24af084c1a4))))) (N (N (N (L 0x1000000000341e844689bf262e0855c) (N (L 0xfffffffffe1e46dd41c624c8a575ee) (L 0x10000000001120b60f5c814fade5226))) (N (L 0xffffffffff66683cbea9d2b7892697) (N (L 0x1000000000054d807f39b4b8d6af2ec) (L 0xffffffffffd1ca4b42472464a97507)))) (N (N (L 0x1000000000018d2e1f0131f2cd623cd) (N (L 0xfffffffffff2d7b55dc74be4a03c8a) (L 0x1000000000006e21085e8cf2f5e1d22))) (N (L 0xfffffffffffc71ebf09f5771c9aec3) (N (L 0x1000000000001d034574f00c212d5a7) (L 0xffffffffffff1618c18b705aaef2eb))))))) (N (N (N (N (N (L 0x10000000000007475cf591ab482026f) (N (L 0xffffffffffffc6b0221256d1641906) (L 0x10000000000001be22fc5586e2de763))) (N (L 0xfffffffffffff295c6e49ae2819c4c) (N (L 0x100000000000006623473a2c57426e0) (L 0xfffffffffffffcfea96a7ed9afc7f8)))) (N (N (L 0x10000000000000166632690ece8236d) (N (L 0xffffffffffffff5ac3f92cc962d07c) (L 0x1000000000000004b69bcad96992a1e))) (N (L 0xffffffffffffffddec148f1c3dd85a) (N (L 0x1000000000000000f3fdebe3416ff6a) (L 0xfffffffffffffff93dbb2c37987b0b))))) (N (N (N (L 0x10000000000000002f7b22bbd88d079) (N (L 0xfffffffffffffffeb585265e0fbe4c) (L 0x100000000000000008e762a5c3e374f))) (N (L 0xffffffffffffffffc322ad5fd17789) (N (L 0x1000000000000000019c68e61c580d7) (L 0xfffffffffffffffff52da81130d47d)))) (N (N (L 0x1000000000000000004813cac8cf6e3) (N (L 0xfffffffffffffffffe23f08a25ac51) (L 0x1000000000000000000c2e766b24a14))) (N (L 0xffffffffffffffffffb0d9b20279d6) (N (L 0x10000000000000000001fe2d194efa1) (L 0xfffffffffffffffffff341621ea57d)))))) (N (N (N (N (L 0x1000000000000000000050df295aa87) (N (L 0xfffffffffffffffffffe02bd166e4e) (L 0x100000000000000000000c6ec5a09f3))) (N (L 0xffffffffffffffffffffb2dfe95b88) (N (L 0x1000000000000000000001daf10da95) (L 0xfffffffffffffffffffff4a8639884)))) (N (N (L 0x100000000000000000000044d933fad) (N (L 0xfffffffffffffffffffffe6104c179) (L 0x100000000000000000000009b3f22eb))) (N (L 0xffffffffffffffffffffffc651a062) (N (L 0x10000000000000000000000154950c7) (L 0xfffffffffffffffffffffff8326c16))))) (N (N (N (L 0x1000000000000000000000002d76fe1) (N (L 0xfffffffffffffffffffffffef8d1fb) (L 0x10000000000000000000000005e9aa0))) (N (L 0xffffffffffffffffffffffffde3585) (N (L 0x10000000000000000000000000bfe6b) (L 0xfffffffffffffffffffffffffbc4f1)))) (N (N (L 0x1000000000000000000000000017bb2) (N (L 0xffffffffffffffffffffffffff7bb2) (L 0x1000000000000000000000000002dd2))) (N (L 0xfffffffffffffffffffffffffff03a) (N (L 0x1000000000000000000000000000566) (L 0xfffffffffffffffffffffffffffe2b)))))))

private def cneg_lf_34 : FastDTree := dleaf cneg_bt_34 0x1000000000001f28c2b9fbabf9f7898 0x100000000000f450912e5fb493e527b 0x100000000000513c654c45682430055 0xfffffffffffc2e907a53ccf21b62dc 0xf64b2a30136c27f7738 0x65a48ab8393bea9d1a5 (M 0x10000000000010ed6412b44fb15de53 0x100000000000ccce7bfce8f2d4c55fd 0x1000000000004c88b608c0a3dfe098a 0xfffffffffffcc84733fa081ba8f5ec 0x100000000000b2c227e2e0f600f8135 0x10000000000242b0149b82243ffa069 0x100000000002b42efe83e2b2f2ffea5 0x1000000000033897f983ce0acdabaa1 0x5c3d0b77a1875904b1d (Q 0xcd8146357e7eca8646c 0x25dab1e80b535e3eb071 0x4349a3e478d4b066ec62)) (M 0x100000000000031c5f84374efad6468 0x100000000000904e27b30b1cee0f5b7 0x10000000000042bce5e36b79343f422 0xfffffffffffdbff824dc2ed8857ea9 0x1000000000003a053e290e600d2a7d3 0x1000000000018deb3c560e702ed81d0 0x100000000001390de92522b30c7249a 0x1000000000026bdecc429b914ac993f 0x4bd45294b358600f744 (Q 0x9056c0fd376cca9990e 0x192206eb6482fa7eb691 0x2b66fcb6a5d44d1efc25)) (M 0xfffffffffffff8d5ab774ef13babb4 0x100000000000673a63a48dd6dd7bc04 0x100000000000392cccaf71eb58db386 0xfffffffffffe75ab892e7010776982 0x10000000000006fb59110dc8393b5e4 0x1000000000010b221d6e25365f5e49e 0x10000000000076348156c0f5c5128e4 0x100000000001b0a0fef072a77d14aec 0x3e42be709ee1cf525c5 (Q 0x673aa752a488fcaa6c7 0x10b397bf2e3b62a64ba9 0x1c07c94a5399c4ea06b0)) (M 0xffffffffffffff457fd2ed7f69a900 0x1000000000004bc9054783df7c70b8b 0x10000000000030626e415dc9f17cb7c 0xfffffffffffef89f6f266d26f21ec2 0xffffffffffff6543b5977ab528b614 0x100000000000b1f74798b6bb98b159d 0x1000000000001b742b7ccef8af1bf22 0x1000000000012044a81f6fff9caa5b7 0x331baa1f9db44c4b4cc (Q 0x4bc90a2d9c7f3c8d28e 0xb23a83e72e3f6e2097e 0x1219296d0037e7a6dc5c))

private def cneg_bt_36 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff9aaf02d44d22e13f144ee) (L 0x100000000188c80b1d868d5bb0a4b7d))) (N (L 0xffffffffb92fc0c02f0521efc19fe7) (N (L 0x100000000a75661cf80579ef7251095) (L 0xfffffffeac9c4ab8c2d05b91de9469)))) (N (N (L 0x1000000026130cb8fdc5416af2bf8e0) (N (L 0xfffffffc248fdb755d03dca068d4ad) (L 0x100000005baee28fad6d7776c261f62))) (N (L 0xfffffff81c7355929f8bb51e4c73e5) (N (L 0x10000000a2712325d36ad0547ff71da) (L 0xfffffff3b375033f03501479cc62b3))))) (N (N (N (L 0x10000000e1ac189a327a6c2a255a60f) (N (L 0xfffffff09d72a6643d6ef0979b2659) (L 0x10000001006a0bc8966b12d80c0a3aa))) (N (L 0xfffffff000f02a57916a2d9674c30b) (N (L 0x10000000f586b30192d01cc2ee5ce59) (L 0xfffffff1d0be1d7fcd14fa459ac0ae)))) (N (N (L 0x10000000ca9a8f656a6a89f1db61164) (N (L 0xfffffff50f8eefcea5b82de0622bda) (L 0x1000000092967af05a1ede950c084bf))) (N (L 0xfffffff88c95b60f9e14bf98be0768) (N (L 0x100000005e47f0c7ce853635c6b84be) (L 0xfffffffb764e820e4ad67cc3eee9ca)))))) (N (N (N (N (L 0x100000003683156b075c12b161fcd63) (N (L 0xfffffffd80df35bfcce47ed1c0f989) (L 0x100000001c992643a070426a5e0b8a1))) (N (L 0xfffffffebfa4c3cf57b5a13add4253) (N (L 0x100000000db86adf8daf6a243115209) (L 0xffffffff6ca50496e6c1a9d232eb32)))) (N (N (L 0x10000000060f602c6f9f540c036005c) (N (L 0xffffffffc169da2d5542a838db0cce) (L 0x10000000027a7b5a6771002e467fe3e))) (N (L 0xffffffffe752577b6a74e3655ac27d) (N (L 0x1000000000f17d6bf44678a1df33332) (L 0xfffffffff6ec67d227eda1330ce807))))) (N (N (N (L 0x100000000055eabf88241ee2c848be5) (N (L 0xfffffffffcdf895d621375eaf02ba1) (L 0x10000000001caf7e7d8898ba3f9a44e))) (N (L 0xfffffffffefcc1bf768a144f3f05bc) (N (L 0x10000000000904ecf1530e2e99a97b9) (L 0xffffffffffb0ce24289e74784d12f4)))) (N (N (L 0x100000000002adcf93025d064038b1a) (N (L 0xffffffffffe91cbb01f701ffcc2214) (L 0x100000000000c0fb5d597d66de2f4bc))) (N (L 0xfffffffffff9b9a6f96584a895b9ed) (N (L 0x1000000000003393e77b5c6637b3097) (L 0xfffffffffffe5d378ec746dccc2179))))))) (N (N (N (N (N (L 0x1000000000000d1fae6eedcd74a7129) (N (L 0xffffffffffff97f1e78e00a7b21781) (L 0x100000000000032f979df92d24c4775))) (N (L 0xffffffffffffe74ee867f263502666) (N (L 0x10000000000000bd44f937e658e9d1a) (L 0xfffffffffffffa64cb41ae6f3150bb)))) (N (N (L 0x100000000000002a10454b4678aa517) (N (L 0xfffffffffffffec7a983a9fb3e7f60) (L 0x1000000000000008f7b3f9a96775287))) (N (L 0xffffffffffffffbebe68dba2c35c26) (N (L 0x1000000000000001d638b6e7b3f071f) (L 0xfffffffffffffff2e43674560fcf9d))))) (N (N (N (L 0x10000000000000005cab1c21d572899) (N (L 0xfffffffffffffffd76f7fb47302f20) (L 0x10000000000000001198482f23894d9))) (N (L 0xffffffffffffffff86fc3a60e6887e) (N (L 0x10000000000000000338fd3deca4559) (L 0xffffffffffffffffea38924ab261f3)))) (N (N (L 0x10000000000000000091ee71b9f51dd) (N (L 0xfffffffffffffffffc3662f8125c8c) (L 0x10000000000000000018f52c0daf41b))) (N (L 0xffffffffffffffffff5ce1c8818f80) (N (L 0x10000000000000000004218ee6e3164) (L 0xffffffffffffffffffe56d942ea43d)))))) (N (N (N (N (L 0x10000000000000000000a99609900ea) (N (L 0xfffffffffffffffffffbcdfa439253) (L 0x100000000000000000001a5e929ce32))) (N (L 0xffffffffffffffffffff5b7ec90bd5) (N (L 0x1000000000000000000003fab67d844) (L 0xffffffffffffffffffffe78941c8db)))) (N (N (L 0x100000000000000000000095520f9eb) (N (L 0xfffffffffffffffffffffc77058047) (L 0x100000000000000000000015468bc71))) (N (L 0xffffffffffffffffffffff80d5be83) (N (L 0x100000000000000000000002f2e9921) (L 0xffffffffffffffffffffffee9c83c5))))) (N (N (N (L 0x10000000000000000000000065db508) (N (L 0xfffffffffffffffffffffffdaf41e9) (L 0x1000000000000000000000000d631ec))) (N (L 0xffffffffffffffffffffffffb31779) (N (L 0x10000000000000000000000001b70c0) (L 0xfffffffffffffffffffffffff64539)))) (N (N (L 0x1000000000000000000000000036db8) (N (L 0xfffffffffffffffffffffffffecc96) (L 0x1000000000000000000000000006b05))) (N (L 0xffffffffffffffffffffffffffdaf8) (N (L 0x1000000000000000000000000000cbd) (L 0xfffffffffffffffffffffffffffba5)))))))

private def cneg_lf_36 : FastDTree := dleaf cneg_bt_36 0x1000000000000defcd39688c5394ff0 0x100000000000de3f4d29ce61c977d6b 0x10000000000045037a45591cf7c5d1e 0xfffffffffffc83a2692ffe13f93860 0xdeaf0a50876f5e3f090 0x58bb95706e3ca75efff (M 0x100000000000026b3b3d53ae341963e 0x100000000000b80679218c9590df888 0x10000000000040f5e4c93d26d268063 0xfffffffffffd10de9da0f3e4541324 0x1000000000008a5cbd1234297d025ee 0x1000000000022d93316f6faaf29c3a6 0x1000000000028547f9c974fa2cccde7 0x1000000000033f25049aa5050730a61 0x5026021d8c1d4043530 (Q 0xb80a8ef8dba38d281a4 0x23e7c640366f0c82a5f5 0x41c3b0a8c5a099b388fe)) (M 0xffffffffffff8f7fe7f02ae9f96477 0x1000000000007e3691d2a9de6f5eded 0x1000000000003874a7e3b7718feacc4 0xfffffffffffdf3a931e907fb9437cb 0x1000000000001c287d0687fd16a06c1 0x100000000001785f88aea1d88b8ffa0 0x10000000000113a93730001241c622c 0x1000000000026990cbf29cd316e46c1 0x4147259c10d84076cad (Q 0x7e68af9b9950b0d405b 0x1796cd2f112fe34170c6 0x2a44bcb871a232f0affc)) (M 0xffffffffffff89b1c389fefecf9506 0x10000000000057c3799995146cc7efb 0x1000000000003023912f5de2d6edbb6 0xfffffffffffe9935e57b804994e6af 0xffffffffffff157f79d41a80100084 0x100000000000f6d65a33c9b246e46b7 0x100000000000599c81c61093576b28e 0x100000000001a97ede2bae7d31d3aab 0x351b0ff7e17f2ce33ed (Q 0x581316cda4b34439bcd 0xf745a9980602d3ae76d 0x1b2d45de72c24808455d)) (M 0xffffffffffffb4e8b4406824a31dd3 0x1000000000003ebb89eda8dfec0864c 0x1000000000002884be511e9e8dc2eee 0xffffffffffff0ffa5a78dbdf0bb31e 0xfffffffffffe6e1649aaa5e99b78fc 0x1000000000009fc211b082c1f85b93c 0x10000000000006462e449ac83b4e6e2 0x100000000001170f5c67410d80debf4 0x2b34db6df4782356bb2 (Q 0x3ee86f524bf46bd1ee2 0xa1b88ef7eded10c492f 0x117216e3dc505558a12d))

private def cneg_bt_38 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff95f8a3b4805a1565bbf35) (L 0x1000000001a750c52598e5daef02351))) (N (L 0xffffffffb1ad6a35916c8a72699de9) (N (L 0x100000000bd4925cc0f1a1b0d25a547) (L 0xfffffffe7825cf84c83b113f83dfb6)))) (N (N (L 0x100000002ccb75988472bd9047b0f5c) (N (L 0xfffffffb61af69b5d4f5988ca35c85) (L 0x100000006f9acfe1a3e122ac280800c))) (N (L 0xfffffff63edf76a2f8de12e69c6426) (N (L 0x10000000cbde7532b7a4de8cb02d98d) (L 0xfffffff057cebb963750b58796fb72))))) (N (N (N (L 0x10000001233e25a068ddadcbd1926c7) (N (L 0xffffffebe1b468a979d714c6c3e21c) (L 0x100000015397e84c9f85afd8d4e0fc3))) (N (L 0xffffffea8d60ed57a796244aede3c7) (N (L 0x100000014d26ae64943fbd81001f4cb) (L 0xffffffec87578707be4390226f7cbe)))) (N (N (L 0x1000000119456684c5eb767fc254d47) (N (L 0xfffffff0a53950c4b85e386648d058) (L 0x10000000cff931ca58efb1e4fc52ecb))) (N (L 0xfffffff551538b53e1ce2c264e552b) (N (L 0x10000000889037af4687c2064de1b92) (L 0xfffffff95c5c554b1cc59190e8cfc1)))))) (N (N (N (N (L 0x10000000508adbab9690ea9f7edfd53) (N (L 0xfffffffc4689917a2ae89d1756f89c) (L 0x100000002b118b918e9bce269b51c99))) (N (L 0xfffffffe190ca431528dbd90c56200) (N (L 0x10000000150be1956f4062bb998e251) (L 0xffffffff1beda2e76757e045cee4a3)))) (N (N (L 0x1000000009766fb7b77d7a03a18c392) (N (L 0xffffffff9d6bb42eb63dbbc35dc59f) (L 0x1000000003eff15394642d0865cb2c3))) (N (L 0xffffffffd876dc8bfd9d8ee89a934b) (N (L 0x10000000018619a2cc89e2f77893cb5) (L 0xfffffffff137a7a978c7d7fa7b6717))))) (N (N (N (L 0x10000000008d1039a931e2ac7400f1b) (N (L 0xfffffffffad33f1a2ac13fa89c36c4) (L 0x10000000002fd9434a16907dc992cb0))) (N (L 0xfffffffffe4c33bd7b60b58f313c92) (N (L 0x10000000000f4743056fb7bcf94e7a1) (L 0xffffffffff78d37fb5efd6d34d05fd)))) (N (N (L 0x1000000000049b5f819822db8cd6710) (N (L 0xffffffffffd8591df99f49782791a5) (L 0x10000000000150c94ba7c7c5794648b))) (N (L 0xfffffffffff4f84a140da0579923a8) (N (L 0x1000000000005b512d7dbd0c7b59553) (L 0xfffffffffffd1548cd7da4cdbc8e20))))))) (N (N (N (N (N (L 0x1000000000001790aa42f5a4e5ff278) (N (L 0xffffffffffff43db5505bbb82d6592) (L 0x10000000000005ccd9ffe97a6fe09a6))) (N (L 0xffffffffffffd2bd5a823fa1803bc1) (N (L 0x100000000000015d47af8f44bd04612) (L 0xfffffffffffff595b4ecaf8c4ae823)))) (N (N (L 0x100000000000004ea9de6ebb98858d4) (N (L 0xfffffffffffffdb40cdbc375c4202c) (L 0x1000000000000010fda666efac3ce0d))) (N (L 0xffffffffffffff838f6f384a1ce67b) (N (L 0x1000000000000003866e823ecef1ffd) (L 0xffffffffffffffe6aec425a5ab2eec))))) (N (N (N (L 0x1000000000000000b41aa96e938bfe2) (N (L 0xfffffffffffffffb0ab31b4e83c264) (L 0x1000000000000000229f95d7f33501b))) (N (L 0xffffffffffffffff10667e3fbb8eb7) (N (L 0x1000000000000000066b62df9626218) (L 0xffffffffffffffffd45a676062e9d5)))) (N (N (L 0x1000000000000000012637759adc9bc) (N (L 0xfffffffffffffffff8517741598eff) (L 0x10000000000000000032eb102d9a52a))) (N (L 0xfffffffffffffffffeb1408c4b6e9c) (N (L 0x1000000000000000000886fa6453ae2) (L 0xffffffffffffffffffc8d537d93510)))))) (N (N (N (N (L 0x10000000000000000001621ccfdce0a) (N (L 0xfffffffffffffffffff730813c034a) (L 0x1000000000000000000037b11013329))) (N (L 0xfffffffffffffffffffea29bbd8e3d) (N (L 0x10000000000000000000087fc728100) (L 0xffffffffffffffffffffcb756fd9e7)))) (N (N (L 0x100000000000000000000142790fd72) (N (L 0xfffffffffffffffffffff852dad799) (L 0x10000000000000000000002e73be38e))) (N (L 0xfffffffffffffffffffffee8d84864) (N (L 0x1000000000000000000000068225f5d) (L 0xffffffffffffffffffffffd96a7e39))))) (N (N (N (L 0x100000000000000000000000e337ebc) (N (L 0xfffffffffffffffffffffffaceb6f8) (L 0x1000000000000000000000001e2e34c))) (N (L 0xffffffffffffffffffffffff51b4c5) (N (L 0x10000000000000000000000003e82e8) (L 0xffffffffffffffffffffffffe9b866)))) (N (N (L 0x100000000000000000000000007e440) (N (L 0xfffffffffffffffffffffffffd38cb) (L 0x100000000000000000000000000f8dc))) (N (L 0xffffffffffffffffffffffffffa972) (N (L 0x1000000000000000000000000001ded) (L 0xfffffffffffffffffffffffffff5b7)))))))

private def cneg_lf_38 : FastDTree := dleaf cneg_bt_38 0xffffffffffffe561cdd0683187f119 0x100000000000cb70a991781470cb254 0x1000000000003b0d9dbd7eec3849860 0xfffffffffffcdda93089e814fd849e 0xcb72634f79237084a21 0x4d78de71a22d90f6c18 (M 0xffffffffffff54ea267ee138ff221d 0x100000000000a654c68ebd0d82ed91d 0x10000000000037877d92414549caddd 0xfffffffffffd5ee9bfb33486283359 0x100000000000655f4763296c5fbe3a0 0x1000000000021b3e0aef98d9f1d5c12 0x100000000002598470e9c0a2fba3b9b 0x100000000003459ce9fc7bd1af96daa 0x45aa41d32635d657f08 (Z (Q 0x96e2021b7806324199e 0x1eb0d084f8e9dcd50978 0x40738d2b7e9db7134889) (S (Q 0xaf30d56f5ce0fded914 0x2420bf89148666ecdd65 0x40738d2b7e9db7134889) (S (Q 0xbcc35800b61c4391576 0x26e9dd97609f82755da2 0x40738d2b7e9db7134889) (Q 0xc65ab9854b4394d9fdf 0x28ca0c1a6f564361ddc2 0x40738d2b7e9db7134889))))) (M 0xfffffffffffefd82624e2a62470cc2 0x1000000000006edc9f74c91866a8581 0x100000000000301701737fd905f7f99 0xfffffffffffe2d7c3d367f05d16a1a 0x10000000000000f8fd81d13ac072894 0x1000000000016592538d6274bc63fd0 0x100000000000f0f60876e6f5d7fcbab 0x100000000002679b5a1e47d5d919110 0x383d17c74047d02d2da (Q 0x7008697b11a8874ae86 0x16592ae40e78404df2eb 0x29515e7b1b3a72a8c499)) (M 0xffffffffffff261ebb3c74e72a9e61 0x1000000000004ab4329b892520f97b0 0x10000000000028cfee72da62c7275c7 0xfffffffffffec3368cda79e3a1ad7e 0xfffffffffffddc3b9900d34127e95f 0x100000000000e529106f0d97b92a913 0x1000000000003f44b3276d28612ba5a 0x100000000001a2fed9458cd40952ad3 0x2d5c8252db6e5408a68 (Q 0x4bef5a059c751e250f9 0xe7b423a9fcbdff72caf 0x1a7bed36b0544a80a9c1)) (M 0xffffffffffff728585c871fccc82be 0x10000000000033c4ae55cf4b54dc580 0x100000000000222c91af3ac03fb7efb 0xffffffffffff2dd7a6615dbcab4b3e 0xfffffffffffd8fb17d61a3aa20762c 0x1000000000008ffcc2e0cbd7e3a2dec 0xffffffffffff2ee6e178f4149cedd1 0x1000000000010ea82ca5cc2307f3d88 0x249c88b18955fed2012 (Q 0x3484a2315cf96af4708 0x952e40d5d5a967f9375 0x10ef8e9f79f45296af0e))

private def cneg_bt_40 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff926fdc5ca6c37c82b9ae9) (L 0x1000000001bf207c09b5bff56f477a4))) (N (L 0xffffffffabab723527d19160c0577c) (N (L 0x100000000cf3e8023589ddbf0e65b6c) (L 0xfffffffe4c60722990bbc9d14fbae7)))) (N (N (L 0x1000000032808fa4ca721539f0f8252) (N (L 0xfffffffab975a4d04ca59c418f29a5) (L 0x100000008110cbee8c7141619bb98ed))) (N (L 0xfffffff49641d6b5cb4f6a2ce45dd6) (N (L 0x10000000f13438779b3bee766351b92) (L 0xffffffed470652b228226538858282))))) (N (N (N (L 0x100000015fd83ee3b5d9be5d6da8e6b) (N (L 0xffffffe774770a10ff4888105e07bc) (L 0x10000001a2461a2dafe5508f660fc5f))) (N (L 0xffffffe556b8d621286332f3b8207b) (N (L 0x10000001a1d8d269e6c671cd18f111a) (L 0xffffffe75da457703df9a7ccc6ddfd)))) (N (N (L 0x1000000166de2d386c900596f3ba58f) (N (L 0xffffffec3f5ff101a81866a7b8406b) (L 0x100000010db28ac4591ba023d18e96d))) (N (L 0xfffffff209c9299d476d193c107fb6) (N (L 0x10000000b3dcc1efb8eb398538e6dc8) (L 0xfffffff73099ae7401c9f09fc6e1be)))))) (N (N (N (N (L 0x100000006baaf83c9652888de77a6af) (N (L 0xfffffffafc330d1a58911fa3839095) (L 0x100000003a66ea992640ce6b21239e1))) (N (L 0xfffffffd6713d5d4950a621fa368e8) (N (L 0x100000001cef7886d353b776682b698) (L 0xfffffffec4535c6a87c754e2a5c61e)))) (N (N (L 0x100000000d2f1db700fc03b2fe8c908) (N (L 0xffffffff75c19f0a61166a1c715b0e) (L 0x10000000058e93886726c53fa7a614e))) (N (L 0xffffffffc7d8fe7663e71a8dde719a) (N (L 0x10000000022d8318277ee1a13c208e1) (L 0xffffffffeabe596a3dcb2727d8730b))))) (N (N (N (L 0x1000000000cc11fd9f42ab2279a7fc2) (N (L 0xfffffffff87811deeb6e0f9d49fb0c) (L 0x1000000000460bc8de757f5e9bd04ba))) (N (L 0xfffffffffd7e4fe549ee714a4f59dc) (N (L 0x100000000016a04896ee187e8a2d876) (L 0xffffffffff36adba585f29d38aefa3)))) (N (N (L 0x100000000006e661201c3b3a54a0acb) (N (L 0xffffffffffc44839708849ec343d4e) (L 0x100000000001fe01aad172cb6a8d987))) (N (L 0xffffffffffef34b6eae2d68bdf599a) (N (L 0x1000000000008bc8bc26cbbeb586654) (L 0xfffffffffffb82e0b7f503dad701ae))))))) (N (N (N (N (N (L 0x1000000000002474950339fdb4e0cda) (N (L 0xfffffffffffedb6c5583c2f8977fb7) (L 0x1000000000000910fa1703a460a4b53))) (N (L 0xffffffffffffb8e444d315106e57ad) (N (L 0x1000000000000227880ec8630195929) (L 0xffffffffffffef78a8d3a2342b9fbc)))) (N (N (L 0x100000000000007d752afb5b268de0a) (N (L 0xfffffffffffffc51ae1f7fae31e988) (L 0x100000000000001b5d520307479d7dc))) (N (L 0xffffffffffffff369d1a6f99611d3a) (N (L 0x1000000000000005bb74709e69e4aaf) (L 0xffffffffffffffd6a2a10528717f77))))) (N (N (N (L 0x100000000000000127a6fea1f526497) (N (L 0xfffffffffffffff7d29baaaf37da84) (L 0x1000000000000000395e2694271e00d))) (N (L 0xfffffffffffffffe712d0aae54547e) (N (L 0x10000000000000000abbfeef61dbe25) (L 0xffffffffffffffffb6af3d63739713)))) (N (N (L 0x100000000000000001f06f0b4b33090) (N (L 0xfffffffffffffffff2fb0535efbeff) (L 0x10000000000000000056ae82fb3da2c))) (N (L 0xfffffffffffffffffdc39fcf62b92e) (N (L 0x1000000000000000000ea4f0c2ff742) (L 0xffffffffffffffffffa0d8dbcdf53d)))))) (N (N (N (N (L 0x1000000000000000000265699e54513) (N (L 0xfffffffffffffffffff0ac2b6948ff) (L 0x10000000000000000000614c3c18127))) (N (L 0xfffffffffffffffffffd9b00f81b56) (N (L 0x100000000000000000000ef95dca191) (L 0xffffffffffffffffffffa30b65303d)))) (N (N (L 0x10000000000000000000023ce1c02b3) (N (L 0xfffffffffffffffffffff24e7abfa4) (L 0x10000000000000000000005333f0cf9))) (N (L 0xfffffffffffffffffffffe09f47962) (N (L 0x10000000000000000000000bc0991f2) (L 0xffffffffffffffffffffffba0c4114))))) (N (N (N (L 0x1000000000000000000000019d9703b) (N (L 0xfffffffffffffffffffffff682c724) (L 0x100000000000000000000000375f29e))) (N (L 0xfffffffffffffffffffffffebef813) (N (L 0x10000000000000000000000007396d5) (L 0xffffffffffffffffffffffffd6a48b)))) (N (N (L 0x10000000000000000000000000eb4a2) (N (L 0xfffffffffffffffffffffffffacd9b) (L 0x100000000000000000000000001d34c))) (N (L 0xffffffffffffffffffffffffff5cd9) (N (L 0x100000000000000000000000000389f) (L 0xffffffffffffffffffffffffffec78)))))))

private def cneg_lf_40 : FastDTree := dleaf cneg_bt_40 0xffffffffffff3b96d2f2bbcd8a2a59 0x100000000000bf184d6a267faa3f64a 0x10000000000034e55689e596b9cefa3 0xfffffffffffd20b8b6cbcb68f99f6d 0xbf7d1e844d4bfba508c 0x4611fa3dc2773622df3 (M 0xfffffffffffec6b825ec762a770c84 0x1000000000009aba2b1f0527041782d 0x10000000000031b30b561114c0856a7 0xfffffffffffd99685447de57333576 0x1000000000004bc61229ae4e8946f2f 0x1000000000020f00aaca9a19d3d8d6b 0x1000000000023a9ab75c5cb6253a32a 0x1000000000034a51707eead7a93940e 0x3ed03b8730747b21147 (Q 0x9bf61499d93e70bf248 0x2146c1a0c5a49bfe3c51 0x3f964b5cdb8b0c2648b5)) (M 0xfffffffffffe9b543eef2a7af47be7 0x10000000000064d354e5adf50c6e2a9 0x1000000000002aed73df92b0fb098d3 0xfffffffffffe59752f2bc1c7bf06ed 0xfffffffffffee487ba4378112d04e6 0x10000000000158faf6848a75fdf6737 0x100000000000d89467bc7149583c574 0x10000000000266442383ad844a92abd 0x32668881463e8ab72e1 (Q 0x6742afb89c5f7dd1a71 0x1596f5db47e11c1ebdef 0x28b5449e374d4b3fc8cb)) (M 0xfffffffffffee3bdae60f555a01b9c 0x10000000000042336126a083b6e2983 0x100000000000244edb2b65252d0c725 0xfffffffffffee3bba685772125f170 0xfffffffffffd0670dbfb493b82299e 0x100000000000d95b09c926abc805714 0x1000000000002ce354681b8723fd15a 0x1000000000019e6f56eb72c8e731dda 0x286c05a39040051e578 (Q 0x448b141c1ea9bc7ad7c 0xde81970c38f4fbbc93a 0x1a0dbdce9af59ec4e04c)) (M 0xffffffffffff46b600a28039425b5d 0x1000000000002ca91db0654a7bc0849 0x1000000000001e4bca908d9098477ac 0xffffffffffff457c8b0191f8d1d918 0xfffffffffffcf90e3225901542e521 0x10000000000085849d2738ba5f2e93d 0xfffffffffffe58d068cefd488a1f7b 0x10000000000108c8668bc08b2917606 0x2076200729979d48406 (Q 0x2e233f9e083b3ffe5c6 0x8e080ed9479eac611c5 0x10a19c10e4a2ba822cc2))

private def cneg_bt_42 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff9014acccc05f16960d80d) (L 0x1000000001cf6f53c262750ad950ae9))) (N (L 0xffffffffa77ac8b0b5da51641de4f8) (N (L 0x100000000dbf82fef977aac65dee489) (L 0xfffffffe2ced98e9a00cc386b1a09c)))) (N (N (L 0x1000000036a7a7e46dc13df69007dfc) (N (L 0xfffffffa3da18f1b6b1ccc703fe14c) (L 0x100000008e0ee4bb0c019e0fdfc3795))) (N (L 0xfffffff357121cd8ef91a78626f124) (N (L 0x100000010d8a6ff97b0f9b63bc06ca5) (L 0xffffffeaede4fae48f9bfa1ec775bd))))) (N (N (N (L 0x100000018eac8292b5af1757f349cc4) (N (L 0xffffffe4015e057299b46986ab2168) (L 0x10000001e0160c306bdcc54e9172918))) (N (L 0xffffffe135f64f2c2af3d325694329) (N (L 0x10000001e56ae19f001ed6cdcf50b4d) (L 0xffffffe3376af228334de71773c89f)))) (N (N (L 0x10000001a5ad55f4d15d7b9b4db2b1a) (N (L 0xffffffe8a9bc5f6851eff3e1ba3486) (L 0x100000014058f4b2ac458e00badb6ec))) (N (L 0xffffffef54502a7505f65f23ea9932) (N (L 0x10000000d7dbdb834dedbaffb46f1dc) (L 0xfffffff55fa7aab419373092b8e4ae)))))) (N (N (N (N (L 0x1000000082803c688c853d3d4f58221) (N (L 0xfffffff9e47406f42d39f032c59c7b) (L 0x100000004776cfa08a8b959c67af531))) (N (L 0xfffffffcce967a93758bf6c515823e) (N (L 0x1000000023bbc41b9dd281d7de2d4b8) (L 0xfffffffe786a2ecc6e2cd6414d7a5c)))) (N (N (L 0x10000000106d319da1662570f915d2d) (N (L 0xffffffff53025f7054cdf2818a9bf0) (L 0x1000000006fbbde1a1c2471d3b98674))) (N (L 0xffffffffb922fd634028421892c574) (N (L 0x1000000002c27d52a4d5c6f2a2cb9e4) (L 0xffffffffe4f408507b4983a8a8d74d))))) (N (N (N (L 0x100000000104b507a78b4f393be45e4) (N (L 0xfffffffff6573172dbdda6f2ed6835) (L 0x10000000005a321a74f360d1b80f70e))) (N (L 0xfffffffffcc283f493412fadb094cc) (N (L 0x10000000001d5c27bce96381f0678fc) (L 0xfffffffffef9c5e23864c7bb22d6d9)))) (N (N (L 0x100000000009055f5c335e1fe04990a) (N (L 0xffffffffffb1a2bcf9914878becf9e) (L 0x1000000000029fb3598045dcf6c7e91))) (N (L 0xffffffffffe9cd2a3eba1b586caf30) (N (L 0x100000000000b96dedaf116885a3a5a) (L 0xfffffffffffa063dea0ea188a99c8d))))))) (N (N (N (N (N (L 0x10000000000030b37930086bc085289) (N (L 0xfffffffffffe77c99d468bef96dd50) (L 0x1000000000000c32114c3acb29a7f39))) (N (L 0xffffffffffffa005dd63c2f20427e8) (N (L 0x10000000000002eaedbd84671d94c7e) (L 0xffffffffffffe98a6f8dbbbb6a2eba)))) (N (N (L 0x10000000000000ab09613f92bf23cb0) (N (L 0xfffffffffffffaf71edda52875f9db) (L 0x10000000000000258cd60c450423acd))) (N (L 0xfffffffffffffeeac3608a694cdf7c) (N (L 0x1000000000000007ea9d628896931e0) (L 0xffffffffffffffc6b14f0469683594))))) (N (N (N (L 0x10000000000000019ae38d12839737d) (N (L 0xfffffffffffffff49998cbce40b0e0) (L 0x10000000000000005039502b5e2863e))) (N (L 0xfffffffffffffffdd091606262b19e) (N (L 0x10000000000000000f1a5c246420969) (L 0xffffffffffffffff98890d1da4823b)))) (N (N (L 0x100000000000000002beae3fa66bb20) (N (L 0xffffffffffffffffed8444b0359d18) (L 0x1000000000000000007b6c4b757f173))) (N (L 0xfffffffffffffffffcce9f8ccf3713) (N (L 0x10000000000000000014f93d933f228) (L 0xffffffffffffffffff7753de409243)))))) (N (N (N (N (L 0x10000000000000000003739a6f1317e) (N (L 0xffffffffffffffffffe9dbb4fd1859) (L 0x100000000000000000008cf3f56b33e))) (N (L 0xfffffffffffffffffffc857784326e) (N (L 0x1000000000000000000015d084c7472) (L 0xffffffffffffffffffff783451b1e6)))) (N (N (L 0x100000000000000000000347372cee3) (N (L 0xffffffffffffffffffffebe2aa281d) (L 0x10000000000000000000007a8d47410))) (N (L 0xfffffffffffffffffffffd1a84f682) (N (L 0x100000000000000000000011676eaca) (L 0xffffffffffffffffffffff98216605))))) (N (N (N (L 0x10000000000000000000000267c2b69) (N (L 0xfffffffffffffffffffffff1d5c125) (L 0x10000000000000000000000052dfcd8))) (N (L 0xfffffffffffffffffffffffe1e426a) (N (L 0x1000000000000000000000000ade7ae) (L 0xffffffffffffffffffffffffc19ddb)))) (N (N (L 0x1000000000000000000000000163d31) (N (L 0xfffffffffffffffffffffffff81eea) (L 0x100000000000000000000000002c64d))) (N (L 0xffffffffffffffffffffffffff0761) (N (L 0x1000000000000000000000000005681) (L 0xffffffffffffffffffffffffffe215)))))))

private def cneg_lf_42 : FastDTree := dleaf cneg_bt_42 0xfffffffffffed2853d40fada17eba9 0x100000000000b792777ad1673ed4c72 0x10000000000031577e89da7d116d45d 0xfffffffffffd4c1526fd75eb1acf8b 0xb8895c2c64d2df94125 0x419c49cc1c8e7fd92f6 (M 0xfffffffffffe6f04611f35a025c4de 0x10000000000093a934f38aa63b9060d 0x1000000000002e558ae0442b3314bc6 0xfffffffffffdbf4949dfb898dd90f4 0x1000000000003baf7f7c19458416c66 0x1000000000020773cb5697ed0c006b8 0x10000000000226d91eb19ee29c2f84c 0x1000000000034d5b1e01812856943bf 0x3ab40b5f29e114943ab (Q 0x95c5ce97bbb057815a0 0x20adebf50a6ad63fa2dd 0x3f0fd65409edb131fdbb)) (M 0xfffffffffffe5f38017fecb2443352 0x1000000000005eba328be2af64f5326 0x10000000000027f384bd8a21295ce18 0xfffffffffffe7604f003ee86d7ee66 0xfffffffffffe29a36d217bc9a3bec8 0x10000000000151341d11a797a0b1c16 0x100000000000c90f7bb4d89598b0286 0x1000000000026566ad218dd6693f385 0x2eee1fc25d301342f5d (Q 0x623e62e2ef4ab3b9e54 0x1527b8f87d0a90f1f749 0x285832ec85b47ee2b09f)) (M 0xfffffffffffebb7286c86f9c42182a 0x1000000000003d0c61498eb585932fc 0x10000000000021b7f1cb5c611d0907d 0xfffffffffffef8eab6f36e178c2d0f 0xfffffffffffc81ac60bc8bf5376afa 0x100000000000d21596f803dc5dddba7 0x10000000000021404aa86b12218683c 0x1000000000019b82ab68248232e49a6 0x25839c370f7d446e59e (Q 0x40548800eca2ddf8b1a 0xd964a1dd979b716b99f 0x19cda08e7faf493a597a)) (M 0xffffffffffff2c633dc3d0849bed95 0x100000000000285dad25a008fb45999 0x1000000000001c1392afbabc2845df9 0xffffffffffff54ec2ede076904709a 0xfffffffffffc9c265e853a1d3c865c 0x1000000000007f19c800c3af2f1777f 0xfffffffffffdd22c9460f4df632562 0x10000000000105096377013e2351945 0x1e0b29c444533efbc1a (Q 0x2a7a3b5f5615acb6c68 0x8a30cf0d9634eb6e604 0x1075acc5bcb2fc1f292e))

private def cneg_sub_4 : FastDTree := (dsplit (dsplit cneg_lf_34 cneg_lf_36) (dsplit cneg_lf_38 (dsplit cneg_lf_40 cneg_lf_42)))

private def cneg_node_5 : FastDTree := dsplit cneg_sub_3 cneg_sub_4

private def cneg_bt_46 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff8db97d3cd9fab0a961530) (L 0x1000000001e016ff0c9b026786f80a4))) (N (L 0xffffffffa32349c9134480bbb9e817) (N (L 0x100000000e952af926152bf16e8c98e) (L 0xfffffffe0b8f3e80322c72812f0606)))) (N (N (L 0x100000003b1b17e57bf86834b06ac94) (N (L 0xfffffff9b7ab90b59bb914045d7f2b) (L 0x100000009c3c8da77a4da37114b6eda))) (N (L 0xfffffff1f7e48422c5d00aed4c5d05) (N (L 0x100000012cf5dc3cca3f077217246c2) (L 0xffffffe84e6c5426963c0166a4cf30))))) (N (N (N (L 0x10000001c35a98c5f95d1ff5723782a) (N (L 0xffffffe0192a4706e20e958f7ea28f) (L 0x10000002268dff3c86f4aac2f69b262))) (N (L 0xffffffdc7992fc7262445c0716661c) (N (L 0x10000002336a36bdccf19214fb19d13) (L 0xffffffde65fb464ce08b64714d13d7)))) (N (N (L 0x10000001ef082f06ea0d5828bd838e2) (N (L 0xffffffe473fddd6f1cd985fc111f5a) (L 0x100000017c293f774049e455c3b7205))) (N (L 0xffffffec1cfe2551bf031c055f3a96) (N (L 0x1000000102d1a64033f184082370818) (L 0xfffffff331ecf216fa1d417cb460f1)))))) (N (N (N (N (L 0x100000009e0717ab6a181fb50e4a269) (N (L 0xfffffff8918bbb8478acbd940ce869) (L 0x10000000575d5e945ff3f440973f226))) (N (L 0xfffffffc141587c45d14472a1076c4) (N (L 0x100000002c161db3c16f733493d4cd6) (L 0xfffffffe1ab74f45b500c2d082e851)))) (N (N (L 0x1000000014725e8698fb3e3b15c5d35) (N (L 0xffffffff27bcf78c6567bad57d4821) (L 0x1000000008c475ea50860ec54f0237f))) (N (L 0xffffffffa6a8aaa2254be03a482dfa) (N (L 0x10000000037e66ba7ba4f8bbe48536e) (L 0xffffffffdd9e919785c9f419d4d875))))) (N (N (N (L 0x10000000014cbc385aa4d233b6a5fba) (N (L 0xfffffffff39f733cf01f381f1f16b5) (L 0x10000000007406e0ebd1480a737f6a6))) (N (L 0xfffffffffbd0d24090539178837613) (N (L 0x1000000000260f6207a7d33b5cfbbbf) (L 0xfffffffffeaac82b835728c3b01c29)))) (N (N (L 0x10000000000bc844d1f9c1df3d4a235) (N (L 0xffffffffff99451e62e946291cef3d) (L 0x10000000000373c57103b4c1d6534b9))) (N (L 0xffffffffffe2afed5f3ccc55e054a3) (N (L 0x100000000000f5bb64ee4e29d5ca2e3) (L 0xfffffffffff80d9439fa34f63d2da8))))))) (N (N (N (N (N (L 0x10000000000040fe8f665ae171e5981) (N (L 0xfffffffffffdf2c10c697d8835a708) (L 0x100000000000106365176c7a0b75c65))) (N (L 0xffffffffffff7e96a4fe567261aac3) (N (L 0x10000000000003f2857c5b849a2e56b) (L 0xffffffffffffe1836f39799abeff9c)))) (N (N (L 0x10000000000000e8efb1a945ce182e9) (N (L 0xfffffffffffff91ee8c9ed8579bb47) (L 0x10000000000000337967843a34d0ddb))) (N (L 0xfffffffffffffe82bc609e6b782da7) (N (L 0x100000000000000aebf622b0ce59c8c) (L 0xffffffffffffffb0afe49f1af165cd))))) (N (N (N (L 0x10000000000000023a73ee332854d9c) (N (L 0xfffffffffffffff01fa4e476cbbe23) (L 0x10000000000000007011fd8848875de))) (N (L 0xfffffffffffffffcf0180c0e9c76dc) (N (L 0x1000000000000000153a3c79086c4aa) (L 0xffffffffffffffff6e23b418ea13dc)))) (N (N (L 0x100000000000000003e194f3937376e) (N (L 0xffffffffffffffffe5c97b8e0382db) (L 0x100000000000000000af8e0e740c942))) (N (L 0xfffffffffffffffffb71f7948ef391) (N (L 0x1000000000000000001e01d1ff5c8a3) (L 0xffffffffffffffffff3be56bbf6c57)))))) (N (N (N (N (L 0x10000000000000000004f779b6de589) (N (L 0xffffffffffffffffffe00c4075ae6f) (L 0x10000000000000000000cbfb3d37148))) (N (L 0xfffffffffffffffffffaf3a11ead5d) (N (L 0x100000000000000000001fbf18cea6a) (L 0xffffffffffffffffffff39d4306a8c)))) (N (N (L 0x1000000000000000000004cc1393640) (N (L 0xffffffffffffffffffffe27bfbe45b) (L 0x1000000000000000000000b451f097f))) (N (L 0xfffffffffffffffffffffbba0bb22f) (N (L 0x100000000000000000000019bf179ac) (L 0xffffffffffffffffffffff65ee2f59))))) (N (N (N (L 0x10000000000000000000000393c9bfb) (N (L 0xffffffffffffffffffffffeae09b5e) (L 0x1000000000000000000000007be7dc0))) (N (L 0xfffffffffffffffffffffffd2ddcf1) (N (L 0x1000000000000000000000001055d50) (L 0xffffffffffffffffffffffffa20023)))) (N (N (L 0x1000000000000000000000000219896) (N (L 0xfffffffffffffffffffffffff41109) (L 0x1000000000000000000000000043686))) (N (L 0xfffffffffffffffffffffffffe8588) (N (L 0x1000000000000000000000000008404) (L 0xffffffffffffffffffffffffffd23a)))))))

private def cneg_lf_46 : FastDTree := dleaf cneg_bt_46 0xfffffffffffe6fb92d4366f807b2d0 0x100000000000b08b16ce5ff75e3aed3 0x1000000000002e2e1b3fc1af47fe340 0xfffffffffffd75d4c2255c83d783ad 0xb24e96f0ced96c83ab7 0x3d835a49b211c8c7d54 (M 0xfffffffffffe1ccb1c4a8c2bae16b7 0x1000000000008d0ffe5fa6e4d5ec5bc 0x1000000000002b57042c0f04644725e 0xfffffffffffde3bf79fc8981f5b085 0x1000000000002c595d9e0a992a5238c 0x10000000000200541c84937c4c34d49 0x10000000000213bd41bd4c58e7426eb 0x100000000003504ca1697f3da9162cf 0x36f0d339cdc04d9b6ef (Q 0x904258df8ca0b56b7ce 0x2023e9b2fae7bd545736 0x3e92db924dcd14074458)) (M 0xfffffffffffe273cf5a0f45e243404 0x100000000000590aee206429a553648 0x100000000000254e18deb5b5669f699 0xfffffffffffe917b837eda02bef3fb 0xfffffffffffd785c1871542c4216ad 0x10000000000149dd1c7b3bcb0a1d2b7 0x100000000000ba19a6dd141d5cd12b6 0x100000000002648aabd5fec57bd2717 0x2bc6e68fec72cf27a18 (Q 0x5dd137d057a94f5c40a 0x14c568718adb6afb2873 0x2803021ee820666d9a34)) (M 0xfffffffffffe9636cb4e12f27ad821 0x100000000000384163fbec1876e2398 0x1000000000001f6bd2fc2f4256e90a9 0xffffffffffff0d3cc40ff162f2b41b 0xfffffffffffc0476915b13e2874ca7 0x100000000000cb3d45ed764f8e1968f 0x10000000000016156b06535ed8e23fd 0x10000000000198a90a4b584da58d67c 0x22e48d9c613005e4498 (Q 0x3ca13872bdc2e3f24d2 0xd4fe94996854c9bf6e8 0x19941b2c49e89d06463f)) (M 0xffffffffffff144a44c95751f89757 0x1000000000002460f7b9f5a9f62b995 0x1000000000001a1d3871348b61ea410 0xffffffffffff63a93ac4411e7c3b3b 0xfffffffffffc451870e4982cb96084 0x1000000000007915d315ec8792968ee 0xfffffffffffd51b14b62fc0d8ec107 0x10000000000101686984c1726a47f10 0x1be1e5b4b51af2b328b (Q 0x273fa1ead0e4cedc4ef 0x86fe9f013f5ee1c4997 0x104f5172f17cf1f7ec95))

private def cneg_bt_48 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff8b5e4dacf3964abcb5253) (L 0x1000000001f1177de85f680b783d8d3))) (N (L 0xffffffff9ea424336775e1131f1ffd) (N (L 0x100000000f753c67241e8d25f253279) (L 0xfffffffde82d47e92114dd704b5d09)))) (N (N (L 0x100000003fdf81f7caa0bc9f6cb472c) (N (L 0xfffffff926da5e4af0990044f3de29) (L 0x10000000abb27e9b78849fa088af1c6))) (N (L 0xfffffff075d102873473ed7ea601b6) (N (L 0x100000014fc53f4ca93936f9b33d299) (L 0xffffffe560fd67ebcaa307872b926c))))) (N (N (N (L 0x10000001fe911433f3292e42518064e) (N (L 0xffffffdbad48821e4386e2f8c76d7a) (L 0x1000000276d2ba1c95562593c7d322f))) (N (L 0xffffffd70bd75a64b1bf63f4e74837) (N (L 0x100000028d5e90aa92ed789204dba12) (L 0xffffffd8cf0087f9525a3a68507360)))) (N (N (L 0x1000000244a0713681554649ad4804d) (N (L 0xffffffdf8358a35da3551784108064) (L 0x10000001c2bb712afc99f4685eb46d5))) (N (L 0xffffffe84c677525a9da044c4725af) (N (L 0x10000001360aef395839d63555d52e7) (L 0xfffffff09583e855c88596d2d4212b)))))) (N (N (N (N (L 0x10000000bf2ea3b371cd83715b01f54) (N (L 0xfffffff6f7599455043db878e281de) (L 0x100000006ab3d79a9efdf17ea6097e3))) (N (L 0xfffffffb3031e4652a60c97b1ed4a5) (N (L 0x100000003657126a371a0824f157f73) (L 0xfffffffda72beefd23c79801167418)))) (N (N (L 0x10000000196d2cb6139b7678b32f465) (N (L 0xfffffffef1e758f074d2d14f9a575b) (L 0x100000000aff22bdfc7c6e967e79c42))) (N (L 0xffffffff8f78db4a15c4d77dff6412) (N (L 0x10000000046b313260dfbdb11b3fe03) (L 0xffffffffd456f0d32bf71bed121f8c))))) (N (N (N (L 0x1000000001a83f5f2a7d47c0ac5191f) (N (L 0xfffffffff027f0ac73e3b4c9da1de9) (L 0x1000000000951bdfb8503de9d867cc2))) (N (L 0xfffffffffa9a11646326c6b235a97d) (N (L 0x1000000000314a18a459720735fddbe) (L 0xfffffffffe446fca7ceccde3090740)))) (N (N (L 0x10000000000f5fa0c74b52f67a90dbf) (N (L 0xffffffffff797667af96b708da9f76) (L 0x10000000000489a2c769d8a44d5e5f9))) (N (L 0xffffffffffd954efdf65d22de7b349) (N (L 0x10000000000145519559ba9df95c294) (L 0xfffffffffff571260c503db21c0956))))))) (N (N (N (N (N (L 0x10000000000056a6c117746c396112a) (N (L 0xfffffffffffd414e9b32ad21ee112b) (L 0x1000000000001600052bc1aee4bf972))) (N (L 0xffffffffffff51aef9da9c4b0a3f09) (N (L 0x1000000000000555bffe8c52e4fc88f) (L 0xffffffffffffd6a8b3669bdb1f0481)))) (N (N (L 0x100000000000013cea48cf48ac89b6d) (N (L 0xfffffffffffff69c251e5406cb10ce) (L 0x10000000000000467d52a7ab1980bdf))) (N (L 0xfffffffffffffdf435df315d26b24e) (N (L 0x100000000000000f0d6b68c9e737167) (L 0xffffffffffffff92581b207e5b7af5))))) (N (N (N (L 0x1000000000000003172b27f5df4352a) (N (L 0xffffffffffffffe9e98920a8d735a1) (L 0x10000000000000009c65c54beeb4514))) (N (L 0xfffffffffffffffbb6ae68d7282c78) (N (L 0x10000000000000001dce080362b2571) (L 0xffffffffffffffff3295750c12b04f)))) (N (N (L 0x1000000000000000057b758c51de5ca) (N (L 0xffffffffffffffffdadd091fb0daa7) (L 0x100000000000000000f97291880d565))) (N (L 0xfffffffffffffffff98251102a8445) (N (L 0x1000000000000000002ae30720cf7dc) (L 0xfffffffffffffffffee6e9f7a7375d)))))) (N (N (N (N (L 0x1000000000000000000723b48936546) (N (L 0xffffffffffffffffffd1f059543daa) (L 0x1000000000000000000126e2b4d7d05))) (N (L 0xfffffffffffffffffff8ae6dc2a873) (N (L 0x100000000000000000002e26ebdc72b) (L 0xfffffffffffffffffffedf1ad5eaef)))) (N (N (L 0x1000000000000000000007033d11005) (N (L 0xffffffffffffffffffffd4bc19b104) (L 0x1000000000000000000001090a5f593))) (N (L 0xfffffffffffffffffffff9b3b6aa45) (N (L 0x1000000000000000000000260c34e78) (L 0xffffffffffffffffffffff1bb58a49))))) (N (N (N (L 0x1000000000000000000000055091a89) (N (L 0xffffffffffffffffffffffe089168e) (L 0x100000000000000000000000b90e842))) (N (L 0xfffffffffffffffffffffffbc6a5c1) (N (L 0x10000000000000000000000018864d3) (L 0xffffffffffffffffffffffff7282d4)))) (N (N (L 0x100000000000000000000000032b2fc) (N (L 0xffffffffffffffffffffffffedf205) (L 0x10000000000000000000000000663e5))) (N (L 0xfffffffffffffffffffffffffdc07e) (N (L 0x100000000000000000000000000c941) (L 0xffffffffffffffffffffffffffba0a)))))))

private def cneg_lf_48 : FastDTree := dleaf cneg_bt_48 0xfffffffffffe12eefbe790e301e1e8 0x100000000000a9f4290af9dc792996b 0x1000000000002b5e893152838d57dc7 0xfffffffffffd9d9e81eb190bf9a468 0xacb99863a4364e9f8a8 0x39c2998cb2ec0a2a867 (M 0xfffffffffffdcfd03821ee0cf0f10d 0x10000000000086e14ad914ede2873b8 0x10000000000028ad4a9360acd4a11c6 0xfffffffffffe0673e8d2766d83eb1f 0x1000000000001dbc9df3df266a4567e 0x100000000001f9956cd7a48a88438c2 0x100000000002013fbfc9a7c52ab3091 0x10000000000353232829e5b0416b574 0x3381cb7259a612f14b4 (Q 0x8b59a390cd7278a7fcc 0x1fa751f80c4b12ae94ae 0x3e1e944a2a5e77da3dd8)) (M 0xfffffffffffdf33359aa37ebfda0c4 0x10000000000053b9c54798192edc5e7 0x10000000000022f3df7b542dbaf3673 0xfffffffffffeab867926a19201d5e8 0xfffffffffffcd05c093b8a71431ab3 0x10000000000142ea88694cbef4cff58 0x100000000000abacabf70fa333b12d5 0x10000000000263acd2de4a140c5352b 0x28ebbe06ba35cd79bed (Q 0x59ebd9e646beb75458f 0x146ea4ec8f5083829aa6 0x27b4f548719a39a59888)) (M 0xfffffffffffe73e3f87f0cf38e4e19 0x10000000000033c806ceabcd4526360 0x1000000000001d61f31627f458158df 0xffffffffffff20645e4fb03d71a3fc 0xfffffffffffb8e908803697aeabf3e 0x100000000000c4c7870efa135af08cd 0x1000000000000b5d885dd74439aa706 0x10000000000195dee28df877c2594e3 0x20897a58856637a92d0 (Q 0x396531adaa40cc18e4a 0xd13a1904fd6dbf39fc0 0x19607a14a17f6c515aad)) (M 0xfffffffffffefe4b38d42070eb43ab 0x10000000000020a9de7fca1c1eb411e 0x1000000000001860dfee752dd800398 0xffffffffffff716b8b5ed7f840e158 0xfffffffffffbf3b84147dedc205012 0x100000000000736f16ee995826120da 0xfffffffffffcd71b285e70a17ba6a8 0x100000000000fde1cf194dddc2bc8b0 0x19f4c605d4f801efb51 (Q 0x246b3de4f3a48daf51b 0x845cd1058a20f5c7c94 0x102dde8b443e21933b9e))

private def cneg_bt_50 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff89031e1d0d31e4d008f77) (L 0x10000000020270d055afa5f6ad21373))) (N (L 0xffffffff99fc86a4d9d43415d84bd0) (N (L 0x10000000106015ac7e7e90890f0a2c6) (L 0xfffffffdc2aebdff3ac51fbd937339)))) (N (N (L 0x1000000044f9c239bdc59e23c401a7b) (N (L 0xfffffff88a697da4bbe249e0eaf651) (L 0x10000000bc8b312787394960f252243))) (N (L 0xffffffeecdb343a2296faeb431d479) (N (L 0x10000001764e7a85424c4ac54b948cc) (L 0xffffffe21d3765ce570fa19133423d))))) (N (N (N (L 0x1000000241115d80e7dfe62ccfde8bf) (N (L 0xffffffd6ad743eff08f0fecb77cbe2) (L 0x10000002d22d50dff6802b3b6d9232d))) (N (L 0xffffffd0d43012ce0337535656d559) (N (L 0x10000002f50626f355ca801842b45a3) (L 0xffffffd2544c0a306eeaf35d246366)))) (N (N (L 0x10000002a86a50306de80871c7708ae) (N (L 0xffffffd9b8b670b9fe7f6fb68f9e35) (L 0x1000000215eba23cb3f10cf9ac63d78))) (N (L 0xffffffe3c710dcd4709f2786625ebe) (N (L 0x1000000173105bac488bbf49b1f12ed) (L 0xffffffed75322c699071a22947c3df)))))) (N (N (N (N (L 0x10000000e713f651622279a65d80e7e) (N (L 0xfffffff50754faa737d30bb39de578) (L 0x100000008232ce4e5770cc1d4beef88))) (N (L 0xfffffffa19ff9605c5f1f2365848f1) (N (L 0x1000000042ea52ccb47d7a5ba9de866) (L 0xfffffffd18d2c5c2d53a4962e1e765)))) (N (N (L 0x100000001f96babe72d817e6478e121) (N (L 0xfffffffeaefdc31f07af4f4d6a015d) (L 0x100000000dc784029b250b0fb78220e))) (N (L 0xffffffff72678767b9e77a4ba7dd2c) (N (L 0x10000000059549ba06b02e173df12e7) (L 0xffffffffc89be1f9e6010814e193c9))))) (N (N (N (L 0x10000000021c66ccda51b7c0fc7bd91) (N (L 0xffffffffebbce97102990118bf1aa9) (L 0x1000000000bf6f837e18f080857e246))) (N (L 0xfffffffff90aea59c3abccac80e5b4) (N (L 0x10000000003fc4dff93b9a94ddfc76c) (L 0xfffffffffdbff6a169e157ae80e507)))) (N (N (L 0x1000000000140a1fc84afa7434c6dd2) (N (L 0xffffffffff4ffb49af5541ac995cdd) (L 0x100000000005f5583a5a017f72f94f0))) (N (L 0xffffffffffcd0a94c9f6399293fe46) (N (L 0x100000000001ae405924161a556a29b) (L 0xfffffffffff1fcb1574dda55152bb5))))))) (N (N (N (N (N (L 0x1000000000007368b00edc3ec4a722d) (N (L 0xfffffffffffc54db4e892e8c7bc62c) (L 0x1000000000001d80f9e6faf9f1cf918))) (N (L 0xffffffffffff156f02e61e987475ad) (N (L 0x1000000000000733fcaeadacbc1a4cc) (L 0xffffffffffffc7ff2720aa5343d1be)))) (N (N (L 0x10000000000001aebbb5d4fab520420) (N (L 0xfffffffffffff3321da08b9ca85488) (L 0x10000000000000606e633525e1d680f))) (N (L 0xfffffffffffffd31237e7eda5f6f0c) (N (L 0x1000000000000014b9668ce768a6190) (L 0xffffffffffffff688c3a16be411afd))))) (N (N (N (L 0x10000000000000044828dcecc1ad74d) (N (L 0xffffffffffffffe14d62305e089b98) (L 0x1000000000000000da08a2c470f359b))) (N (L 0xfffffffffffffffa018a894bccc351) (N (L 0x100000000000000029ce0e8cd5c7d0a) (L 0xfffffffffffffffedf02583439cdcd)))) (N (N (L 0x100000000000000007bc609735572b9) (N (L 0xffffffffffffffffcb71239b4135c9) (L 0x1000000000000000016213709828da6))) (N (L 0xfffffffffffffffff6c26d8cf9d86b) (N (L 0x1000000000000000003d3b37aef2999) (L 0xfffffffffffffffffe6d85a95a250f)))))) (N (N (N (N (L 0x1000000000000000000a408a65de937) (N (L 0xffffffffffffffffffbdab36a56607) (L 0x10000000000000000001a9db929f8a9))) (N (L 0xfffffffffffffffffff566ae37b903) (N (L 0x10000000000000000000430643cc0d8) (L 0xfffffffffffffffffffe5b493d2dd6)))) (N (N (L 0x100000000000000000000a3d97ae4a8) (N (L 0xffffffffffffffffffffc0a57cfbf4) (L 0x100000000000000000000185286e73a))) (N (L 0xfffffffffffffffffffff6ba469a20) (N (L 0x1000000000000000000000382ad4c7e) (L 0xfffffffffffffffffffffeae166186))))) (N (N (N (L 0x100000000000000000000007e33fe22) (N (L 0xffffffffffffffffffffffd12debe5) (L 0x1000000000000000000000011418cb5))) (N (L 0xfffffffffffffffffffffff9ae7325) (N (L 0x10000000000000000000000024c7dcd) (L 0xffffffffffffffffffffffff2b40fd)))) (N (N (L 0x10000000000000000000000004c6dae) (N (L 0xffffffffffffffffffffffffe4b699) (L 0x100000000000000000000000009aeb0))) (N (L 0xfffffffffffffffffffffffffc95ca) (N (L 0x100000000000000000000000001327b) (L 0xffffffffffffffffffffffffff9532)))))))

private def cneg_lf_50 : FastDTree := dleaf cneg_bt_50 0xfffffffffffdbbd7aec888b0e8c212 0x100000000000a3c13a7de6ed3e48d50 0x10000000000028de4d2346e8f6ab951 0xfffffffffffdc3315eb29b6ceb4b5d 0xa7b89da19b7a5ee7de6 0x3654d8c4760dcc0f938 (M 0xfffffffffffd87cc82f8c6d404a846 0x10000000000081115b41b020cfb0867 0x100000000000264e55eb0f2d17439e5 0xfffffffffffe2726f85538c9cd1b64 0x1000000000000fd1ed954a38267dce3 0x100000000001f32c97a91e7e752eb17 0x100000000001ef596b3062b4f981343 0x10000000000355dc4ca51a45bdc31ce 0x306193cad1ac66637a3 (Q 0x86fb08232af6f958964 0x1f36cc4b6c116bb6a91d 0x3db244c665285f373b5f)) (M 0xfffffffffffdc2e0edb6204f717201 0x1000000000004ebc5324d3f296fd72e 0x10000000000020dba5e7217f4fc106a 0xfffffffffffec3e987426fb556c73c 0xfffffffffffc314898afe985b923f0 0x1000000000013c51e6b5928651c2e51 0x1000000000009dc2728db5d200ede8a 0x10000000000262ca3d7370d1c8b2d4c 0x2656f7a403aeacbf595 (Q 0x56803697fb9025623b8 0x14222013f47f93c20f7d 0x276d5b8294b303244618)) (M 0xfffffffffffe5449b3465581328ce0 0x1000000000002f9728239b839dc3917 0x1000000000001b91df9348c4cd73e88 0xffffffffffff3229153b71c0c3334f 0xfffffffffffb1fb5f144447a0ca755 0x100000000000beaaa3b2b99c1a1b690 0x10000000000001138df5653039171bb 0x1000000000019321050cf28c42918c4 0x1e6c7dc2c477a3b63dd (Q 0x36959dacbe4eea2671f 0xce02da3f162e119bf82 0x19321673cbcceafbc24a)) (M 0xfffffffffffeea3d1847775fc6166b 0x1000000000001d3069bae3e57d6a661 0x10000000000016d6c2a2acd4ac99c42 0xffffffffffff7dfee4b06aee9f723b 0xfffffffffffba7d3ee0a788b488608 0x1000000000006e1cad62c185d027afc 0xfffffffffffc6227a46b4259e2ffeb 0x100000000000fa7245a052dcd2155a8 0x183dc44c13b62f0fe3f (Q 0x21f623f570030eb2184 0x823782a3e37de022847 0x1010b5d514c00a319447))

private def cneg_bt_52 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff86a7ee8d26cd7ee35cc9a) (L 0x10000000021422f6548bbc2925a308a))) (N (L 0xffffffff952b9fd291c53b6f702a98) (N (L 0x1000000011561719e24e8e7f5e2f9bb) (L 0xfffffffd9af9c8f2561f353170c4e1)))) (N (N (L 0x100000004a6ef0a44b8c0c2be125186) (N (L 0xfffffff7e188bb0e0b4e3ac49dcdb9) (L 0x10000000cee2fb80e2fbcf5bb71f3a2))) (N (L 0xffffffecfc2665b1471a768280b4ec) (N (L 0x10000001a0ef219af3f26861aa7d87b) (L 0xffffffde79e6303a7f63cd8623ca4b))))) (N (N (N (L 0x100000028bb1904a04bb46e9cd68e5e) (N (L 0xffffffd107894f90048c1b62336c18) (L 0x100000033a0f57746ff49c2250094aa))) (N (L 0xffffffc9b6d3979fa60300d61f7c67) (N (L 0x100000036c5cceae7f2b231c13e2091) (L 0xffffffcad34ca5c03eb1f32754950e)))) (N (N (L 0x100000031ca62b1207f25d81b39169a) (N (L 0xffffffd2f00ebd50d0c45ab955667f) (L 0x1000000277e4dade37c44500a787023))) (N (L 0xffffffde6cc2a42f6e1980679b7cb0) (N (L 0x10000001bbb0c1248e5639c499c62aa) (L 0xffffffe9b7cfb7719c68d1895513f4)))))) (N (N (N (N (L 0x10000001170aaa14fab4dd5c6c52693) (N (L 0xfffffff2b01737075c26dd127eee12) (L 0x100000009eb85c62b8adb505b135a52))) (N (L 0xfffffff8c6b4dacad1b8d92b64d862) (N (L 0x100000005252b66d1be644e17b4aa84) (L 0xfffffffc699e64d79de7979af05d33)))) (N (N (L 0x1000000027351535ee0b0329fdd510b) (N (L 0xfffffffe5be725fd64a81161539a1e) (L 0x10000000113ff018ed45622bea28ef9))) (N (L 0xffffffff4dffc75a0dbd1d70539fbb) (N (L 0x10000000070c330e00e8702171acce6) (L 0xffffffffb9cb59420333c2be0521a0))))) (N (N (N (L 0x1000000002afb096abab0528f46cabe) (N (L 0xffffffffe61cf2d33dd5a47399b81e) (L 0x1000000000f589a3f54ae77046e2d89))) (N (L 0xfffffffff70ab7de664384c86e53b1) (N (L 0x1000000000526bde9d7c93de2e78627) (L 0xfffffffffd14a95d0954f7ab74b8ba)))) (N (N (L 0x10000000001a189181b6f59a9c3d0f9) (N (L 0xffffffffff19f04f03ef31ae80e982) (L 0x100000000007d0f27bdb23d1483bde4))) (N (L 0xffffffffffbce93d7c5db9990b3a62) (N (L 0x1000000000023876e2718101b1dcc8c) (L 0xffffffffffed6b8fd866db41042be6))))))) (N (N (N (N (N (L 0x100000000000998e9167bf2b621245a) (N (L 0xfffffffffffb1a19507ea35511f9dc) (L 0x1000000000002786f85e055c414c345))) (N (L 0xfffffffffffec4ad29e69a61d7ddb2) (N (L 0x10000000000009b72e15fec810e63ad) (L 0xffffffffffffb435ecf802bcf823ac)))) (N (N (L 0x1000000000000248d64dbc2f95b920d) (N (L 0xffffffffffffee8ed0bc44fe7fc65c) (L 0x1000000000000083c949ea2320d7ab5))) (N (L 0xfffffffffffffc266b2ab306c04218) (N (L 0x100000000000001c8111a96e42778ad) (L 0xffffffffffffff2f087d261a3e0725))))) (N (N (N (L 0x1000000000000005ed2cc91577a0918) (N (L 0xffffffffffffffd5612f6afbf25c4b) (L 0x10000000000000012fa667dd215c0ce))) (N (L 0xfffffffffffffff7a0740732395aeb) (N (L 0x10000000000000003a9390e65ba16ef) (L 0xfffffffffffffffe69d952e46c42b1)))) (N (N (L 0x10000000000000000ae793c56ad2972) (N (L 0xffffffffffffffffb5b169eb923471) (L 0x100000000000000001f61274899f595))) (N (L 0xfffffffffffffffff2dbd83a021758) (N (L 0x10000000000000000057550f6f22fa6) (L 0xfffffffffffffffffdc04cfe62d50c)))))) (N (N (N (N (L 0x1000000000000000000eb4e0b6e7ef9) (N (L 0xffffffffffffffffffa093d45842c9) (L 0x10000000000000000002665ce6ecc01))) (N (L 0xfffffffffffffffffff0aaa11f3790) (N (L 0x10000000000000000000613c448fef6) (L 0xfffffffffffffffffffd9bf51f130d)))) (N (N (L 0x100000000000000000000ef055ad628) (N (L 0xffffffffffffffffffffa353df79dd) (L 0x10000000000000000000023acd99734))) (N (L 0xfffffffffffffffffffff25ce16288) (N (L 0x100000000000000000000052d45a1f0) (L 0xfffffffffffffffffffffe0c59a116))))) (N (N (N (L 0x10000000000000000000000bb1acc6a) (N (L 0xffffffffffffffffffffffba66d93b) (L 0x1000000000000000000000019b7e3a9))) (N (L 0xfffffffffffffffffffffff68ee9ae) (N (L 0x100000000000000000000000371a94b) (L 0xfffffffffffffffffffffffec0722e)))) (N (N (L 0x1000000000000000000000000731808) (N (L 0xffffffffffffffffffffffffd6cdc4) (L 0x10000000000000000000000000ea7b9))) (N (L 0xfffffffffffffffffffffffffad174) (N (L 0x100000000000000000000000001d23b) (L 0xffffffffffffffffffffffffff5d1c)))))))

private def cneg_lf_52 : FastDTree := dleaf cneg_bt_52 0xfffffffffffd6a1c63bd43ddc375ae 0x1000000000009de75cfd2805aa36690 0x10000000000026a33ea961097464aec 0xfffffffffffde662b953d036d9c656 0xa33b8d8d6205942f61c 0x333458fab98272facff (M 0xfffffffffffd44710d8734cc8cea01 0x1000000000007b95e563d6024a70778 0x10000000000024306c693c31de0e163 0xfffffffffffe45aede8440fa81e49a 0x1000000000000291cbd93780857db8c 0x100000000001ed0f7bf5113d537fd2f 0x100000000001de034d468006fdadc9b 0x10000000000358760ebfbe366bd94e7 0x2d8a4214470dbe3d027 (Q 0x83177e3fbf827d4dd61 0x1ed1136c2cf7e673f98c 0x3d4d3cabbd30380ede27)) (M 0xfffffffffffd96041c503e91afa743 0x1000000000004a0988e095a24741ef4 0x1000000000001efc80246cbd89854ae 0xfffffffffffeda7d189acd21ef3ea1 0xfffffffffffb9ac3849637938fef77 0x1000000000013609a7f8be2f96c9e04 0x10000000000090550b2b269888c2f39 0x10000000000261e0682fe6bedf79ddb 0x240268ec860acc552c5 (Q 0x5381abeb791b3cff1cb 0x13dea00b9d602321dcc5 0x272b90244db5d23d923e)) (M 0xfffffffffffe3730c79f63899f764d 0x1000000000002ba6e0889b07f576772 0x10000000000019f36651016e16912ca 0xffffffffffff42661a87458599dd7a 0xfffffffffffab79e533dbb3398b497 0x100000000000b8ddb839ee65ba4c29c 0xffffffffffff73283e450a4df6be86 0x100000000001906c9eb8fbe55b3afa7 0x1c8747c0ffa1255b341 (Q 0x3428df8d5d5f8b8e5cc 0xcb45cedd3b3ab865e19 0x19085670f42290036ea9)) (M 0xfffffffffffed7f093b1e3b9430fd1 0x10000000000019edc2e219382d28db1 0x1000000000001577555f20c3c68a237 0xffffffffffff8941a87ab10cd5f405 0xfffffffffffb6135113a7c96865110 0x10000000000069166d10c03552334f4 0xfffffffffffbf2955f2d4cc4960182 0x100000000000f716d47b8605dda7a79 0x16b682942dd2bdf35f6 (Q 0x1fdab2072aada5f1f92 0x807c0785404d03e0994 0xff746b5dca3653d9293))

private def cneg_bt_54 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff844cbefd406918f6b09bd) (L 0x1000000002262defe4f3aaa2e1c3015))) (N (L 0xffffffff90309e71b6aeb8cb717b7a) (N (L 0x100000001257a2ed1ed675acecf71d2) (L 0xfffffffd70f3abbd67c5c597fcd203)))) (N (N (L 0x1000000050446321b17ebdb7053d2fa) (N (L 0xfffffff72b5b99d8dc9c9fe7c2a0cb) (L 0x10000000e2d82cc9af7ce3c3e4a434f))) (N (L 0xffffffeafd80757410b1532f15085e) (N (L 0x10000001d00d17f83d90554a5653d44) (L 0xffffffda6cef829ce792eb05487056))))) (N (N (N (L 0x10000002df5e82efe8a9559a18ba361) (N (L 0xffffffcaa750ae4ade03ed5d5233d2) (L 0x10000003b017873d9ae787cf03cb821))) (N (L 0xffffffc1945d546c8c6360ce50681f) (N (L 0x10000003f5a4006581eb9698175c017) (L 0xffffffc2247446a95393d8219b0693)))) (N (N (L 0x10000003a3eb936dd973d52bec274db) (N (L 0xffffffcaffa68a61f1990e017d83c7) (L 0x10000002eb2d97eddc4757ce1a56a59))) (N (L 0xffffffd817c033bade25279238d86f) (N (L 0x10000002120d349d41f7a00deb2bf4c) (L 0xffffffe53f93a39dd38bdebb0032b8)))))) (N (N (N (N (L 0x1000000150a6ed5e2bf9098807d2d0b) (N (L 0xffffffefdccf75b17a45426e367d36) (L 0x10000000c14f83a58677e244b13376b))) (N (L 0xfffffff729494db7e5c230400e4d20) (N (L 0x10000000652f1050c679f4fe402695c) (L 0xfffffffb922d25de8d3e4c144bb91e)))) (N (N (L 0x10000000309e0f5568c7a0425ade677) (N (L 0xfffffffdf4d36c2cb0a2075c3f4c82) (L 0x100000001592da5074129de6fdd8095))) (N (L 0xffffffff20729172686df745a24a51) (N (L 0x1000000008e344fd0cf83344ad30265) (L 0xffffffffa71a64ecfcc52189f58dce))))) (N (N (N (L 0x10000000036a470ad74907c65af4022) (N (L 0xffffffffdef57055fc2769adfebf88) (L 0x10000000013a9fb71ff67051c6a27c1))) (N (L 0xfffffffff47a19a724518b9907cc3a) (N (L 0x10000000006a6ceaa6699c596f264ba) (L 0xfffffffffc375df973363d8fd45f4b)))) (N (N (L 0x100000000021f30e4acc0a87e824888) (N (L 0xfffffffffed3994f5f80d03d3aed4d) (L 0x10000000000a3e4114d7c6ce6d0c3d0))) (N (L 0xffffffffffa7c32a0aecae4e21d23c) (N (L 0x100000000002ee55299daf2327c704c) (L 0xffffffffffe763a9c5b28d52cd3e9f))))))) (N (N (N (N (N (L 0x100000000000cc1c7d19a3909b0661b) (N (L 0xfffffffffff977847ddbbfcbc9f14d) (L 0x10000000000034e72d35d4611d00c09))) (N (L 0xfffffffffffe588a3f5f4c38d2c07f) (N (L 0x1000000000000d175bf2c8ebd4ab68e) (L 0xffffffffffff9989844ee82053a2bb)))) (N (N (L 0x100000000000031946a9ddf9608d941) (N (L 0xffffffffffffe843960f59b8fc1c43) (L 0x10000000000000b3ec0782bbb38b40b))) (N (L 0xfffffffffffffaba1a71326e0d388a) (N (L 0x10000000000000272a4132dcae46229) (L 0xfffffffffffffedff834c5d94b7644))))) (N (N (N (L 0x100000000000000831c3112e6074268) (N (L 0xffffffffffffffc4e2f47c27002996) (L 0x1000000000000001a67475802a414fd))) (N (L 0xfffffffffffffff450a5ec7c0cec5b) (N (L 0x100000000000000051fe1bf20e0ee56) (L 0xfffffffffffffffdc5c638a9d4b416)))) (N (N (L 0x10000000000000000f5b07d73e52fdf) (N (L 0xffffffffffffffff970d4b2d0ea8df) (L 0x100000000000000002c732599d194cf))) (N (L 0xffffffffffffffffed54a4f7856626) (N (L 0x1000000000000000007c6e59663eb71) (L 0xfffffffffffffffffcc96019350106)))))) (N (N (N (N (L 0x10000000000000000015131c60b0287) (N (L 0xffffffffffffffffff76de791dc336) (L 0x100000000000000000037564c35e112))) (N (L 0xffffffffffffffffffe9d7066cd01f) (N (L 0x100000000000000000008ceaef5b896) (L 0xfffffffffffffffffffc868a8e2dea)))) (N (N (L 0x1000000000000000000015c515d5025) (N (L 0xffffffffffffffffffff7894d9ae1e) (L 0x1000000000000000000003445d0712c))) (N (L 0xffffffffffffffffffffebf6d4c803) (N (L 0x10000000000000000000007a0552c5a) (L 0xfffffffffffffffffffffd1df83c50))))) (N (N (N (L 0x10000000000000000000001151b2089) (N (L 0xffffffffffffffffffffff98a6b1e0) (L 0x10000000000000000000000264a54ef))) (N (L 0xfffffffffffffffffffffff1e7f3c8) (N (L 0x1000000000000000000000005277f47) (L 0xfffffffffffffffffffffffe2084de)))) (N (N (L 0x1000000000000000000000000ad2376) (N (L 0xffffffffffffffffffffffffc1de81) (L 0x100000000000000000000000016289d))) (N (L 0xfffffffffffffffffffffffff82530) (N (L 0x100000000000000000000000002c481) (L 0xffffffffffffffffffffffffff07d9)))))))

private def cneg_lf_54 : FastDTree := dleaf cneg_bt_54 0xfffffffffffd1d617b97919cf71052 0x100000000000985d18e052b04ba9255 0x10000000000024a3adc68e6e9797bb0 0xfffffffffffe071c832fcbfbd0921b 0x9f3417498a121c33e39 0x305adfc9b83e4a59769 (M 0xfffffffffffd056a40c2b58a71394f 0x1000000000007666059d1cd3a564181 0x100000000000224a47b5c27e3860018 0xfffffffffffe61f5da888e727f3ad2 0xffffffffffff5f49f08e769de8b307 0x100000000001e734f1b4fac14195d0d 0x100000000001cd36a99fddef2416423 0x1000000000035aeecc7c6771bc6009d 0x2af579a69af1af261d8 (Q 0x7fa1b81afbbda3459d2 0x1e74f76acf0eb0cecb4e 0x3ceed7128579020b44d2)) (M 0xfffffffffffd6c56e7c029bc94b133 0x1000000000004599a08b5e7f414a752 0x1000000000001d4decd2f9cc0089659 0xfffffffffffeef2c9a086a056bbe55 0xfffffffffffb0c6c2cc1b049425a5c 0x10000000000130091ea5345195a865a 0x100000000000835eb2efcd6f30d364c 0x10000000000260ed2a72927afc2a516 0x21e788fed179d0cda5a (Q 0x50e51ea2d42ceda471e 0x13a301f3aca1680ddd22 0x26eefac80686c2473561)) (M 0xfffffffffffe1c5def1db5974d28c8 0x10000000000027f0769daea7c672bcd 0x100000000000187eb85cba20d023fe0 0xffffffffffff5108a5ffc05373f6c4 0xfffffffffffa55fe3c3c9026303024 0x100000000000b358acbaafa322a6d3b 0xfffffffffffedb592e3ca0e4c968c3 0x1000000000018dbf32b98001a1799dc 0x1ad341390ea38b31774 (Q 0x321697707352c3a960d 0xc8f16eb858f31c91c5e 0x18e2ad1fe13dd73cfb65)) (M 0xfffffffffffec732af78e657ef65d2 0x10000000000016dc2959aabf8d1efa6 0x100000000000143b69f6c24847d0f0c 0xffffffffffff93234e9693b5f9c29b 0xfffffffffffb1fa1dfa2aa2f9c9b93 0x1000000000006454e36766dc68f89b9 0xfffffffffffb88245e16fc5c112198 0x100000000000f3ccd3dbd1a0f75cc97 0x1558774c9d712a7ea32 (Q 0x1e146bb2130982d6a64 0x7f19393600fdaaf2712 0xfe10e2ace650f66a593))

private def cneg_bt_56 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff81f18f6d5a04b30a046e0) (L 0x10000000023891bd06e77163e181214))) (N (L 0xffffffff8b0ab1376ff66dd566fd92) (N (L 0x1000000013651d51258ccaf53c4a121) (L 0xfffffffd4480bf9c96f9f065d4712b)))) (N (N (L 0x10000000567fafaedb8ef54e15b3904) (N (L 0xfffffff666f8bfead85bf492317b3a) (L 0x10000000f88b2ab109bd5dda0a093c5))) (N (L 0xffffffe8cdcda5d5fe39593e513bde) (N (L 0x100000020417390f76e95c804c6443b) (L 0xffffffd5eb3e97ffcb6ed8943b6623))))) (N (N (N (L 0x100000033d1dfc8a8f0c4d6f6ce27aa) (N (L 0xffffffc376485ec3278cc0e6004e6d) (L 0x100000043616e2f16c56e37a6ea29e7))) (N (L 0xffffffb8495d5a891a13be95b3dd92) (N (L 0x10000004936bd8dce30fbb210afe0a7) (L 0xffffffb81a896fe220edbfedccc7b0)))) (N (N (L 0x100000044135d7601b48d5d08f1ab81) (N (L 0xffffffc1b734797e2ce809c8d29b33) (L 0x1000000372b634a9752d4832380826b))) (N (L 0xffffffd09be002c059c742a643a314) (N (L 0x1000000278a7163dbb970a168f7bd1d) (L 0xffffffdfe94240ae2f2c53595c9987)))))) (N (N (N (N (L 0x1000000195c95af5cbe6d67896f4c83) (N (L 0xffffffec749d0ac8f7172c38331edf) (L 0x10000000eb38f757d9db1c423b91fc4))) (N (L 0xfffffff532020a51d4d002780857c3) (N (L 0x100000007c3ffd54317881be9996916) (L 0xfffffffa89809ad781449b6cfe4674)))) (N (N (L 0x100000003c3ab763bc3fcd6258b095e) (N (L 0xfffffffd75125ed8ecb9fe1d1ebc75) (L 0x100000001af4b0f8740f76fbcd9f31e))) (N (L 0xfffffffee7817c1894a1361a9ff6f2) (N (L 0x100000000b3298f05485cbd0ecab820) (L 0xffffffff8f8b18d8f4b12987f382a9))))) (N (N (N (L 0x1000000004566c8074962c5b52c7f38) (N (L 0xffffffffd5de28621228d0ca1f1c7c) (L 0x100000000192c257b2f20b87cda191f))) (N (L 0xfffffffff13127b4d235adefcdd1db) (N (L 0x100000000089496f20a243c5230ffbc) (L 0xfffffffffb19c4bd093cbc26b0b4a9)))) (N (N (L 0x10000000002c1f8b17a5f58363db3ca) (N (L 0xfffffffffe78232411e07f4f5beb1a) (L 0x10000000000d691b543553d3410954c))) (N (L 0xffffffffff8c0fa044633e61b2c1d1) (N (L 0x100000000003dd68adacaf51e1f88a6) (L 0xffffffffffdf6ee0fb335337bb469d))))))) (N (N (N (N (N (L 0x1000000000010f0a5e06cdf22c59295) (N (L 0xfffffffffff74b6b3331b3c21b95d8) (L 0x10000000000046bc15be506f376fbdc))) (N (L 0xfffffffffffdc7e2ea73db430ffa98) (N (L 0x100000000000119f4a74b6e289c2e78) (L 0xffffffffffff759d614284aad145f8)))) (N (N (L 0x1000000000000432ecdc591514a1d97) (N (L 0xffffffffffffdfbb4221bbeee6a402) (L 0x10000000000000f5647c1902b3fbfd6))) (N (L 0xfffffffffffff8c8fba059b81f758c) (N (L 0x1000000000000035c249b2500bd6388) (L 0xfffffffffffffe73649ca2fd7d3d87))))) (N (N (N (L 0x100000000000000b519737c9664c3a1) (N (L 0xffffffffffffffae1817ab52b32b0e) (L 0x10000000000000024b257beab3bf902))) (N (L 0xffffffffffffffefb5c41faa236bc2) (N (L 0x100000000000000072a71832ffc4837) (L 0xfffffffffffffffce03bcf59b29c72)))) (N (N (L 0x10000000000000001599eea381dc58c) (N (L 0xffffffffffffffff6bed5b62fd073e) (L 0x100000000000000003ee655637d0c27))) (N (L 0xffffffffffffffffe58110f4b195fe) (N (L 0x100000000000000000b11b8bfd7b434) (L 0xfffffffffffffffffb69bf45a36868)))))) (N (N (N (N (L 0x1000000000000000001e2b4e45792d9) (N (L 0xffffffffffffffffff3b220b88ea01) (L 0x10000000000000000004faad51344ff))) (N (L 0xffffffffffffffffffe001d451630f) (N (L 0x10000000000000000000cc035c09159) (L 0xfffffffffffffffffffaf4b7dda50b)))) (N (N (L 0x100000000000000000001fb11593b01) (N (L 0xffffffffffffffffffff3a52b0c6a9) (L 0x1000000000000000000004c833deaf5))) (N (L 0xffffffffffffffffffffe2980529c6) (N (L 0x1000000000000000000000b391ab690) (L 0xfffffffffffffffffffffbbefe039f))))) (N (N (N (L 0x1000000000000000000000199f908bd) (N (L 0xffffffffffffffffffffff66b18a84) (L 0x1000000000000000000000038f2dade))) (N (L 0xffffffffffffffffffffffeafbcb04) (N (L 0x1000000000000000000000007b4b3c0) (L 0xfffffffffffffffffffffffd314e1b)))) (N (N (L 0x1000000000000000000000001042f24) (N (L 0xffffffffffffffffffffffffa264f0) (L 0x1000000000000000000000000217804))) (N (L 0xfffffffffffffffffffffffff41b28) (N (L 0x100000000000000000000000004338a) (L 0xfffffffffffffffffffffffffe8659)))))))

private def cneg_lf_56 : FastDTree := dleaf cneg_bt_56 0xfffffffffffcd5497b4ed5b9409730 0x100000000000931a58d1816d4823a18 0x10000000000022d68346cb32eabea81 0xfffffffffffe255b30e3ecb30d3c02 0x9b95b95f0ca0b50b122 0x2dc1d43325b041b35e0 (M 0xfffffffffffcca62ac13aec5477ab4 0x100000000000717a2b746383a92de86 0x100000000000209334ce0ccdce06f45 0xfffffffffffe7bf834b6a49a281e45 0xfffffffffffe9f2c72c1ee4d97dedf 0x100000000001e194be04b3792969ddf 0x100000000001bced00b17758020ea79 0x1000000000035d453aacd1e8a564a3d 0x289c8b471d048777fee (Q 0x7c8e26939749af8e291 0x1e215f0465a6d0d9f9a3 0x3c967a7c51bd05ca6d4b)) (M 0xfffffffffffd459193576ab51ed80f 0x10000000000041660b12e5dd21f93d9 0x1000000000001bc7f423b49a3174826 0xffffffffffff01f49385ee96311815 0xfffffffffffa85e0b48abe22f54795 0x1000000000012a4874e82690d1a2be4 0x10000000000076d9d69054d616a0afb 0x1000000000025feeafcb72a4e6a4461 0x1fff96d77dbdfe05092 (Q 0x4ea0f7879d76ace24d4 0x136e3b7baf0ec9aeeef4 0x26b70f266f5aeb282e38)) (M 0xfffffffffffe039456d10d9210a5fe 0x100000000000246e4e34b598ed47520 0x100000000000172c87f411c14e7abab 0xffffffffffff5e0e25aefff66efb95 0xfffffffffff9fa8857af2cddb38952 0x100000000000ae142c6f0a702b97ff4 0xfffffffffffe498078f52646948519 0x1000000000018b16948ed23798787de 0x1949b8bfb12184a0559 (Q 0x30578dc78f2a771b876 0xc6f5d42562648513013 0x18c09a4d130feb658b54)) (M 0xfffffffffffeb7cf27f2cff0ca1a86 0x10000000000013f6e28e89dcf55b070 0x100000000000131c4c49e0c5c812e3d 0xffffffffffff9ba2aa4b4586d76e40 0xfffffffffffae2de305e5fff4dc4c2 0x1000000000005fd14d76af6b4616083 0xfffffffffffb229643324a851e881a 0x100000000000f091e790c6158d1b2ee 0x141d1fe38fe53e29100 (Q 0x1c9fb0598642faf006c 0x7dffa99ae55be0d9a0c 0xfcd967c5012d64f1a98))

private def cneg_bt_58 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff7f965fdd73a04d1d58404) (L 0x10000000024b4e5dba67106c24dd683))) (N (L 0xffffffff85b906d8e5021c38db700a) (N (L 0x10000000147eec5e0a16a97b40c7917) (L 0xfffffffd15846f835279185ceb23b7)))) (N (N (L 0x100000005d26ae877cca0dd4cda5cc8) (N (L 0xfffffff593695c386075749616945d) (L 0x10000001101e9076d52cd58e10eb4d1))) (N (L 0xffffffe668cb402a472744d6946e26) (N (L 0x100000023d860c44cfe1c22a81ff383) (L 0xffffffd0e8ae378894893940810409))))) (N (N (N (L 0x10000003a6111cad5b2e11dff22e2fd) (N (L 0xffffffbb5b65debd3e0dcd844ea7ca) (L 0x10000004ce1665018110a014f70ab32))) (N (L 0xffffffadaddb50080751e4bc037f4a) (N (L 0x10000005489d31488ad2e19fc95b26a) (L 0xffffffac81e2454b745a85c573a205)))) (N (N (L 0x10000004f7f240bb8c018e08ad72310) (N (L 0xffffffb6dee55f46f396ec4b8ac7df) (L 0x1000000411e97edf2ce120e80fc0297))) (N (L 0xffffffc7c57f11102422521e78d1a7) (N (L 0x10000002f27069d58813c9b1b2d6dfa) (L 0xffffffd98b376b72dd5e6c6e04901e)))))) (N (N (N (N (L 0x10000001e8acea4d229154868f9ac96) (N (L 0xffffffe859cb66a76b842c3811b5b6) (L 0x100000011df58ec5345b04c38b2dffe))) (N (L 0xfffffff2cde7356513a3a9c3defccd) (N (L 0x10000000986edd691978713d1664c95) (L 0xfffffff944a5fa40b1f1b377a078fb)))) (N (N (L 0x100000004a8b873ff54665d775f2327) (N (L 0xfffffffcd6e18efc5646ee943486db) (L 0x1000000021a6268af0397921f706085))) (N (L 0xfffffffea0649f7dbcb8dc5dfceaf1) (N (L 0x100000000e182e0d9c065350538574b) (L 0xffffffff71e00d818d4ace036fdcdb))))) (N (N (N (L 0x10000000058101a8c2413bd11817255) (N (L 0xffffffffca53bcd06ac8e537492177) (L 0x10000000020316779b84d629122e28f))) (N (L 0xffffffffecfd2d2816326635ec94ad) (N (L 0x1000000000b0ed1787e4854715e7888) (L 0xfffffffff9a989a0a31c7f2dc7e2eb)))) (N (N (L 0x1000000000394a3fa3fd27b1ee06d98) (N (L 0xfffffffffe0153cd9dc522ac7cc355) (L 0x1000000000118a4bdd3b77414608f88))) (N (L 0xffffffffff67cffdbbcd203e01e9a7) (N (L 0x100000000005176130f88fd418f947c) (L 0xffffffffffd4f280468eb98d10b93e))))))) (N (N (N (N (N (L 0x100000000001678fa045d53d3dea4fa) (N (L 0xfffffffffff4695a9a39daac5794d8) (L 0x1000000000005e7baadba4166c2b3f8))) (N (L 0xfffffffffffd06936a41b7678b2485) (N (L 0x10000000000017b2a4bd2725b4644a5) (L 0xffffffffffff4548daaa93d9baead2)))) (N (N (L 0x10000000000005af1e5b2af8c7c5002) (N (L 0xffffffffffffd42cf2a1ba0cbac221) (L 0x100000000000014e59f1ad7f1aba9a3))) (N (L 0xfffffffffffff623538edd8d0a983f) (N (L 0x1000000000000049b778ecc9374b485) (L 0xfffffffffffffdde6fe27a44d5b253))))) (N (N (N (L 0x100000000000000f9e57130773b6b8c) (N (L 0xffffffffffffff8ea0d09f792cf34b) (L 0x10000000000000032f3774ea5078ffc))) (N (L 0xffffffffffffffe9502db4ac957df7) (N (L 0x1000000000000000a028e2406aa173b) (L 0xfffffffffffffffb9f6e9aacdff1ef)))) (N (N (L 0x10000000000000001e5b41ee93455d4) (N (L 0xffffffffffffffff2f4b675e0d08c9) (L 0x1000000000000000058eac26e11afb7))) (N (L 0xffffffffffffffffda6f628e3cba58) (N (L 0x100000000000000000fbd3993d88f84) (L 0xfffffffffffffffff9758827e7c5d2)))))) (N (N (N (N (L 0x1000000000000000002b24e0b108add) (N (L 0xfffffffffffffffffee5aa3eed1199) (L 0x10000000000000000007293bbcaf418))) (N (L 0xffffffffffffffffffd1dbddb41099) (N (L 0x10000000000000000001270e29fca75) (L 0xfffffffffffffffffff8af4c604a5c)))) (N (N (L 0x100000000000000000002e1689ba8a7) (N (L 0xfffffffffffffffffffedfbd3f0505) (L 0x1000000000000000000006fe0a18c6c))) (N (L 0xffffffffffffffffffffd4e2c2ad9b) (N (L 0x100000000000000000000107fc23e21) (L 0xfffffffffffffffffffff9bac4f27b))))) (N (N (N (L 0x100000000000000000000025deae094) (N (L 0xffffffffffffffffffffff1cd2b328) (L 0x10000000000000000000000549c5f56))) (N (L 0xffffffffffffffffffffffe0b18c84) (N (L 0x100000000000000000000000b82334b) (L 0xfffffffffffffffffffffffbcbde87)))) (N (N (L 0x100000000000000000000000186959d) (N (L 0xffffffffffffffffffffffff731f29) (L 0x1000000000000000000000000327fc5))) (N (L 0xffffffffffffffffffffffffee0235) (N (L 0x1000000000000000000000000065f01) (L 0xfffffffffffffffffffffffffdc1e0)))))))

private def cneg_lf_58 : FastDTree := dleaf cneg_bt_58 0xfffffffffffc91779ca6447ad4ddab 0x1000000000008e185141d982bc6a676 0x10000000000021335b980eeffac8c57 0xfffffffffffe412b842b71d6f90a0d 0x9855b3baaa0802145e2 0x2b62627780104778509 (M 0xfffffffffffc930584fe9db1479b02 0x1000000000006ccc01e2fe0153cfaa3 0x1000000000001f032e81122e8f076e9 0xfffffffffffe93c215d916c527cf2a 0xfffffffffffde84aee6da169b47c45 0x100000000001dc27864cbace7e47c7b 0x100000000001ad2011da3c64cb850af 0x1000000000035f785dc4131e17799ed 0x26789beb752a6e6fbca (Q 0x79d2e75cfb95298c274 0x1dd5486224de093f07e2 0x3c4398aa279d201a69b5)) (M 0xfffffffffffd216d01ea4293d685bc 0x1000000000003d695a0a2fa073d3000 0x1000000000001a6341950167ee4bbbc 0xffffffffffff12e098d32d058647c8 0xfffffffffffa06bf07b88a29dc11a0 0x10000000000124c0a18952650b60743 0x1000000000006ac114c14964bed3d43 0x1000000000025ee3717d5308183bae1 0x1e43c597d2a7722a00b (Q 0x4cad09ee2c58c672511 0x133f5b97c6176de87d60 0x26834ccccc594fd3efa2)) (M 0xfffffffffffdec97ddc2988170e53f 0x100000000000211bd364756e71c61b4 0x10000000000015f6217bdf9db94a581 0xffffffffffff698245f4511530dcbe 0xfffffffffff9a4ee68c496ef593483 0x100000000000a9099c1ed4dac18dc18 0xfffffffffffdbd5551a807751595df 0x1000000000018870e23edc6ca80a291 0x17e41373748d177acaf (Q 0x2ee5883817cd75c1a9d 0xc544ca1cda41bcc9fee 0x18a1aa148c7ed4fe4395)) (M 0xfffffffffffea992914241e17ca81d 0x100000000000113a2625b9c82977137 0x1000000000001213da747cd21bd5bbc 0xffffffffffffa2cc080e60a712f0e5 0xfffffffffffaaaac6c326194f1c9d1 0x1000000000005b858fb9b8d2dea74ea 0xfffffffffffac1ae7bbec024790a6c 0x100000000000ed63f9d949bf01fd6bd 0x12fe3481926ae6caf60 (Q 0x1b794e914e19204c514 0x7d21b9adabf5adbd135 0xfbc76ba72d65afa0548))

private def cneg_bt_60 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff7d3b304d8d3be730ac127) (L 0x10000000025e63d1ff7287bbabd7d6a))) (N (L 0xffffffff803ace0b3d3785a15991e3) (N (L 0x1000000015a578190247c2a162c4711) (L 0xfffffffce3e13392655aaf315e683a)))) (N (N (L 0x10000000643f7c5cd9c3c03792b7bf4) (N (L 0xfffffff4afa88814bfebc2fe1daa3c) (L 0x1000000129b74f5f52f8683c260d00e))) (N (L 0xffffffe3c9e249a50ef6a59cf0cb05) (N (L 0x100000027cdc851ccd2877eb173e0ff) (L 0xffffffcb57f10aba9ebe04860d6580))))) (N (N (N (L 0x100000041b76f8e26611b0341fe749f) (N (L 0xffffffb23ad2adea63c57d6232296f) (L 0x100000057a5d45ed805720008f86345))) (N (L 0xffffffa194cb4b9bf60067bf15bd31) (N (L 0x100000061884ee7cee94e97de722b5b) (L 0xffffff9f1f8664e4965f4c5d6e0eb4)))) (N (N (L 0x10000005cc104167d3f1d6d2f5138db) (N (L 0xffffffaa363d0b58fb769a87123338) (L 0x10000004ccbfc4cdff87ed93b5c1830))) (N (L 0xffffffbd584a76a1ab11eb82e4e24d) (N (L 0x1000000382ded84683f65a68cf79270) (L 0xffffffd1f4475305e10ebd03eb45b6)))))) (N (N (N (N (L 0x100000024bf7524db7917b81b42b46e) (N (L 0xffffffe368ea63c17bc7c36b07a131) (L 0x100000015b52aea495555295af46a3b))) (N (L 0xffffffefe61ea818305522f341e3b5) (N (L 0x10000000bad631d33d32d1d782a52eb) (L 0xfffffff7b64c84b08c761b748327cb)))) (N (N (L 0x100000005c2d77dc6ee6110f9282008) (N (L 0xfffffffc132f5c7fd6ad3a95cfb1c0) (L 0x1000000029f6fd45ea47797cfbbc7e4))) (N (L 0xfffffffe47aa7fe998de4ac8f679b3) (N (L 0x1000000011b951aec97468a0e33d5dd) (L 0xffffffff4c8ce0ef44c732f85ce490))))) (N (N (N (L 0x1000000006fa2cbd83d268a825c0e3d) (N (L 0xffffffffbbb0c1a46f9230c65fe659) (L 0x1000000002921d2b407272bac8491a0))) (N (L 0xffffffffe79dcbc1f13710a7c37064) (N (L 0x1000000000e3ca8021299b8bf603552) (L 0xfffffffff7cf397c44c7204a0ae875)))) (N (N (L 0x10000000004a505d443ffb52d15d322) (N (L 0xfffffffffd672430bbf1feaab52fa6) (L 0x100000000016eb51b09b3d55138e2fc))) (N (L 0xffffffffff386cf74aad93ed884b7a) (N (L 0x100000000006b34dbde556b7a32f042) (L 0xffffffffffc7241882d2df4a7f98e7))))))) (N (N (N (N (N (L 0x100000000001dc85f3dc52017251877) (N (L 0xfffffffffff096bea5117b28562998) (L 0x1000000000007e14845b30f9b5d8ee4))) (N (L 0xfffffffffffc047f4439b3db0828d2) (N (L 0x1000000000001fd6267770eaa0ad62a) (L 0xffffffffffff0453527b83a92e07ec)))) (N (N (L 0x10000000000007afd31651556ee2378) (N (L 0xffffffffffffc48a65b98f9f9acb01) (L 0x10000000000001c71ac1dcbc36fdb2b))) (N (L 0xfffffffffffff2887e3bfe77ad6591) (N (L 0x1000000000000064fb8099024d9c08b) (L 0xfffffffffffffd124a241a2eb3c7d5))))) (N (N (N (L 0x100000000000001587b43e035f3d8ce) (N (L 0xffffffffffffff633b59b32ce6c008) (L 0x10000000000000046abcc7c0ff5f06f))) (N (L 0xffffffffffffffe06fb2baade37106) (N (L 0x1000000000000000df80b96752dbb4f) (L 0xfffffffffffffff9df8a3155e9235e)))) (N (N (L 0x10000000000000002a9df1202b02d19) (N (L 0xfffffffffffffffeda21f78c0ea161) (L 0x100000000000000007d91728cc32703))) (N (L 0xffffffffffffffffcacbc248391d7c) (N (L 0x10000000000000000165b4195f64c4a) (L 0xfffffffffffffffff6aeaacf86063c)))))) (N (N (N (N (L 0x1000000000000000003da2d5452b6a5) (N (L 0xfffffffffffffffffe6b8182df4958) (L 0x1000000000000000000a49d8eb34800))) (N (L 0xffffffffffffffffffbd859b833bac) (N (L 0x10000000000000000001aa49b90ef8d) (L 0xfffffffffffffffffff566dfc1f630)))) (N (N (L 0x1000000000000000000042f482585a4) (N (L 0xfffffffffffffffffffe5c142db438) (L 0x100000000000000000000a36b6f0702))) (N (L 0xffffffffffffffffffffc0da4d8751) (N (L 0x100000000000000000000183af35a05) (L 0xfffffffffffffffffffff6c4491b4a))))) (N (N (N (L 0x100000000000000000000037e9647b7) (N (L 0xfffffffffffffffffffffeafb4e78d) (L 0x100000000000000000000007d945151))) (N (L 0xffffffffffffffffffffffd169e97a) (N (L 0x10000000000000000000000112b89cb) (L 0xfffffffffffffffffffffff9b65708)))) (N (N (L 0x100000000000000000000000249bacf) (N (L 0xffffffffffffffffffffffff2c3240) (L 0x10000000000000000000000004c1da1))) (N (L 0xffffffffffffffffffffffffe4d04c) (N (L 0x100000000000000000000000009a6c5) (L 0xfffffffffffffffffffffffffc9819)))))))

private def cneg_lf_60 : FastDTree := dleaf cneg_bt_60 0xfffffffffffc5192093a444aa3030f 0x10000000000089516453c42d8a518d5 0x1000000000001fb29c031b2e9bfc6a6 0xfffffffffffe5aa83994c380978049 0x956ae7e3a939d505058 0x2935a4cc23ab5462edc (M 0xfffffffffffc5f00d32d52cda9f090 0x1000000000006856541f77f98fd381b 0x1000000000001d92f2637c10774a8e8 0xfffffffffffea96d423f560345640a 0xfffffffffffd3a2da6734c6c5ae451 0x100000000001d6e6c2ab7961beda4ed 0x1000000000019dc9dcdb12bb9acf10e 0x100000000003618782d44561f26b53b 0x2482cfb656082eacb3b (Q 0x7767a0ea4e24a54dc11 0x1d8fc93ab5f33b3d41b3 0x3bf5ae57bcc9ba9a9ea3)) (M 0xfffffffffffcffa4c46459a8fb7988 0x100000000000399f260bf7fa94a7c09 0x10000000000019193856336b04dfb2a 0xffffffffffff22091dd3e2b355ac90 0xfffffffffff98ea5c2a5600100a37b 0x1000000000011f6b5c005e3a6acf1aa 0x1000000000005f0f4017f64c10e5098 0x1000000000025dca301efcc61a54b05 0x1cad6b0f70643cb0889 (Q 0x4b026791504867374e9 0x13158a73aa2cc515fd09 0x26533eb531a6ceff5013)) (M 0xfffffffffffdd72f07047e4734ed21 0x1000000000001df5624fb6271881c8a 0x10000000000014d57f4b3e63454db2f 0xffffffffffff737cdd696445cc61ff 0xfffffffffff954e22a6429abb910cb 0x100000000000a4330fb89d6f6974e80 0xfffffffffffd3691782aa413a5dac5 0x10000000000185cc7e96986c3bf11a1 0x169bfd2455d7a704893 (Q 0x2dbb0d535dbf9dcf0f9 0xc3d1ca03b2f77297f47 0x18857457916b27c24997)) (M 0xfffffffffffe9c4c2df88ccaed7e87 0x1000000000000ea306fa23e8fbafb2f 0x100000000000111c97fb71bda5f4251 0xffffffffffffa8b72f3b08d53ea8c8 0xfffffffffffa76ce6440c040f31124 0x100000000000576c2d0be1923722ad6 0xfffffffffffa653266ff2ca104271e 0x100000000000ea41363fa715cdf0a20 0x11f5d722fe9c9fcd668 (Q 0x1a9e0215cededff1020 0x7c73989e5952b33170e 0xfad520ffd8daaa2a315))

private def cneg_sub_6 : FastDTree := (dsplit (dsplit (dsplit cneg_lf_46 cneg_lf_48) (dsplit cneg_lf_50 cneg_lf_52)) (dsplit (dsplit cneg_lf_54 cneg_lf_56) (dsplit cneg_lf_58 cneg_lf_60)))

private def cneg_bt_63 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff7ae000bda6d78143ffe4a) (L 0x100000000271d219d609d75276706c4))) (N (L 0xffffffff7a8f35839ffc6bba6c2249) (N (L 0x1000000016d92a7466225e097e4b379) (L 0xfffffffcaf788c8e0bee012e49102b)))) (N (N (L 0x100000006bd07c9744b521f5ed4ee34) (N (L 0xfffffff3baa2a33e493ad2ae23b481) (L 0x10000001457cd0a2ce29a041b3ee776))) (N (L 0xffffffe0ec21daa0eebcd85dfc0180) (N (L 0x10000002c2a8d063705391010c0ee2f) (L 0xffffffc52a781fc4e3c2e7fc017a4e))))) (N (N (N (L 0x100000049eaf74084ee423bb11f356a) (N (L 0xffffffa7f5a268ddde93c4c1e23508) (L 0x100000063d77e9053d8d28e41eff35c))) (N (L 0xffffff93cb73268f5272d27fa1906e) (N (L 0x1000000706e0a9f98910fd79bc54682) (L 0xffffff8fb0348a1b3844d38cb78dad)))) (N (N (L 0x10000006c213cbcaaf06944008352f4) (N (L 0xffffff9b72ce72ad69f022f8e4da9a) (L 0x10000005a7d4b69ccc2fc4ffc1e4acf))) (N (L 0xffffffb10dd8cc4e0838ccd9077c1c) (N (L 0x100000042e01c3cef2dfcc702aac486) (L 0xffffffc8ea6eed69151448dd0e4707)))))) (N (N (N (N (L 0x10000002c2cc486d6f6e1872937ee07) (N (L 0xffffffdd77bcb06a814cf8ff42285a) (L 0x10000001a579046c8e0c66ae4f13d0d))) (N (L 0xffffffec5f26b41cbf982904ab7ced) (N (L 0x10000000e4cba5759b6e33ee311a4fb) (L 0xfffffff5ce464bb6f4e9bc989f3ac8)))) (N (N (L 0x1000000071e0263fa731cfc989891c6) (N (L 0xfffffffb2150cf49dac5420e349323) (L 0x1000000034497176b028337b4a1d803))) (N (L 0xfffffffdd910ad134abd9218f1e0a0) (N (L 0x1000000016445bc091fbab8f38678d3) (L 0xffffffff1da306d8ef20bd33da8039))))) (N (N (N (L 0x1000000008d62964d4741ee290ea07f) (N (L 0xffffffffa9251b9c77ade92629700a) (L 0x1000000003480db13f36d18c4f36dcc))) (N (L 0xffffffffe0c1618abb5e09173551e9) (N (L 0x100000000124ff7b785dc144dfa844c) (L 0xfffffffff56cdb04043f3614b28fcb)))) (N (N (L 0x1000000000604db65b0678b3bd6568d) (N (L 0xfffffffffc9f3d4149dff6ebc5177a) (L 0x10000000001deb327511bbdd0b74112))) (N (L 0xfffffffffefa89cb7b12049ddef772) (N (L 0x100000000008cf36e68311c08750a63) (L 0xffffffffffb4fb098ee1c35fabfc12))))))) (N (N (N (N (N (L 0x10000000000276ea0d8de4e3e6c2683) (N (L 0xffffffffffeb86778ab673f6cda6c6) (L 0x100000000000a8141c2d1df184ab8dc))) (N (L 0xfffffffffffaac4a0613ed45397d47) (N (L 0x1000000000002aba674af96f5652624) (L 0xfffffffffffead1a2d45ff41423ceb)))) (N (N (L 0x1000000000000a628b54ade39948289) (N (L 0xffffffffffffaf68615be6b958f7af) (L 0x100000000000026ada4086d31fe0700))) (N (L 0xffffffffffffeda10790b13c522e32) (N (L 0x100000000000008a31ea9ef380bae9a) (L 0xfffffffffffffbfac7da7c89619634))))) (N (N (N (L 0x100000000000001da64484c496e2e99) (N (L 0xffffffffffffff27710e35b963fe4a) (L 0x10000000000000061ecd61244ccfe78))) (N (L 0xffffffffffffffd421594229a1d408) (N (L 0x1000000000000001379582fcfb527d4) (L 0xfffffffffffffff76ed6b7159d533e)))) (N (N (L 0x10000000000000003bc4d2215153f2f) (N (L 0xfffffffffffffffe62a39fdb8ecf2e) (L 0x10000000000000000b125a8589b7666))) (N (L 0xffffffffffffffffb4b8e38a1fb534) (N (L 0x100000000000000001fb943eba0b83a) (L 0xfffffffffffffffff2bd78eeb69c6c)))))) (N (N (N (N (L 0x10000000000000000057f6dec59fc55) (N (L 0xfffffffffffffffffdbd150ab3165f) (L 0x1000000000000000000ec43f29cd5a7))) (N (L 0xffffffffffffffffffa051b527abfb) (N (L 0x100000000000000000026742756f6e8) (L 0xfffffffffffffffffff0a94f987548)))) (N (N (L 0x10000000000000000000612b9f670cc) (N (L 0xfffffffffffffffffffd9ce948807b) (L 0x100000000000000000000ee765b67c8))) (N (L 0xffffffffffffffffffffa39b3ea7a0) (N (L 0x100000000000000000000238c306d76) (L 0xfffffffffffffffffffff26aff5b51))))) (N (N (N (L 0x10000000000000000000005276c07d5) (N (L 0xfffffffffffffffffffffe0eb19e6c) (L 0x10000000000000000000000ba313c8c))) (N (L 0xffffffffffffffffffffffbabf7587) (N (L 0x10000000000000000000000199711ca) (L 0xfffffffffffffffffffffff69ac9e7)))) (N (N (L 0x10000000000000000000000036d76b5) (N (L 0xfffffffffffffffffffffffec1e4ca) (L 0x1000000000000000000000000729b98))) (N (L 0xffffffffffffffffffffffffd6f64a) (N (L 0x10000000000000000000000000e9b02) (L 0xfffffffffffffffffffffffffad541)))))))

private def cneg_lf_63 : FastDTree := dleaf cneg_bt_63 0xfffffffffffc1543bcbb4a93b440fd 0x10000000000084c1030f909c72d52b3 0x1000000000001e4d823ffcb1eaddf70 0xfffffffffffe71f7a68aa3439bc1f2 0x92cdab810883a4a2b7a 0x2734ce1410402080456 (M 0xfffffffffffc2e0745996779d5f8e9 0x1000000000006414efbb2380d21c913 0x1000000000001c3c1036b490b51c55e 0xfffffffffffebd1ec4ea4eb945dbe3 0xfffffffffffc945f4681bd9507298b 0x100000000001d1ccafd4e22be933cc5 0x1000000000018ee4a2c7200a9943d37 0x100000000003637238c1047659807eb 0x22b475e0c5c6cf3245e (Q 0x754550a42363595a7f9 0x1d500e71ada7b9bb3c3e 0x3bac42e03b80639e25a9)) (M 0xfffffffffffcdff8d53391036d3495 0x1000000000003603f281e222392aff7 0x10000000000017e4024aefb78e2fff5 0xffffffffffff2f913ab78c8d2fe859 0xfffffffffff91d34fdc492f74a724a 0x1000000000011a430ff4e61e70f33cf 0x10000000000053bf60689f08768b101 0x1000000000025ca1ed654443ddbddc3 0x1b362c6b50cbb22a0b5 (Q 0x499b273e86ab88bd687 0x12f008c5106bdd4c8b6e 0x26267ac6e5f02deaeff1)) (M 0xfffffffffffdc3249c0b321eb0c26d 0x1000000000001af82c6460085107e75 0x10000000000013c55841a63ec081d15 0xffffffffffff7c1fc85863f926a113 0xfffffffffff90a1614861937f13342 0x1000000000009f8b3f4c70adb876c53 0xfffffffffffcb4f1543a4dc8915c25 0x10000000000183280b89ac718d8de45 0x156b93236d4ae626340 (Q 0x2cd31ed00145937dd42 0xc291ec620c864257a33 0x186b9c18d99ece9074ba)) (M 0xfffffffffffe8fcf7936fea4382f5c 0x1000000000000c2f59a69eb39356743 0x1000000000001031bbedf03e619114b 0xffffffffffffad85533b2037c19595 0xfffffffffffa47061004ebca8bd5c3 0x10000000000053803cf96699732c390 0xfffffffffffa0ce9759c10f8f7e16f 0x100000000000e728048a36ab0e22778 0x10feb97763126b9602b (Q 0x1a09f35359af2fd1156 0x7beb30b083b2cc0545a 0xf9fd6f8701a094df288))

private def cneg_bt_65 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff7884d12dc0731b5753b6e) (L 0x10000000028599353e2cff3084a728f))) (N (L 0xffffffff74b56bf734b6902f9de060) (N (L 0x10000000181a6f4fafd75994e31c24e) (L 0xfffffffc782aff54089800da96926b)))) (N (N (L 0x1000000073e05ba24b505c89a437749) (N (L 0xfffffff2b334aa8d30c7be74fc1f38) (L 0x10000001639918e5e29443e762edd4c))) (N (L 0xffffffddca3924229ac2fcca958aab) (N (L 0x100000030f852f08782ab9862266ab2) (L 0xffffffbe5057786e127fb407ae4189))))) (N (N (N (L 0x10000005313e5405d55213d6839bef5) (N (L 0xffffff9c6981e9a82a5f2cc84a3a85) (L 0x100000071a3f7f62bddc09e8e55812f))) (N (L 0xffffff8418beaa542c08f571aa3bad) (N (L 0x1000000817ecdb45aa629d5e6ef5cc7) (L 0xffffff7de7489fbed59d6ee0fcb924)))) (N (N (L 0x10000007df2a1d96c8dce91c2df3abe) (N (L 0xffffff8a3ec5ccf7ca68181b6af789) (L 0x10000006a88081615af653fc151a842))) (N (L 0xffffffa2940c4f1b502d35ee9f226c) (N (L 0x10000004f89be8dc1aff25b30a1e809) (L 0xffffffbe294c5178713fd0c8640287)))))) (N (N (N (N (L 0x1000000350e416d2c0778d176b1eb88) (N (L 0xffffffd653f50a09e43b6afd4c0c5d) (L 0x10000001fefdfeac81acd83a72f11fe))) (N (L 0xffffffe817eb0ec4535537c8655785) (N (L 0x1000000117ec112ac017c6089742c8e) (L 0xfffffff378ef104da68f6b721d7599)))) (N (N (L 0x100000008c8d41e2ff538a3ae8732bf) (N (L 0xfffffff9f6a77df40cb8a24861c6a5) (L 0x10000000411664adc6a483f00c0343e))) (N (L 0xfffffffd4f5379941408e6412eb66f) (N (L 0x100000001bf2d20de276473660da449) (L 0xfffffffee2ba0c9c55dcce20423c9d))))) (N (N (N (L 0x100000000b2e4af6340c126d8f32919) (N (L 0xffffffff91ab3badf97d50b0286c56) (L 0x10000000042f463d3e5abd0527f7565))) (N (L 0xffffffffd800808434aae754640114) (N (L 0x10000000017882e2e9820c531f901db) (L 0xfffffffff25c277e5d55169fadcc7a)))) (N (N (L 0x10000000007cae20b85145c1826f73c) (N (L 0xfffffffffb9c50c8c2885c74bc80c9) (L 0x10000000002704aa2a8c8f99dad5989))) (N (L 0xfffffffffea9ca8de7dea5b915a286) (N (L 0x10000000000b9231269177caeaf5c54) (L 0xffffffffff9d1dbd12a89ede27cf83))))))) (N (N (N (N (N (L 0x100000000003428357b6ed5a9e6925b) (N (L 0xffffffffffe4d3140379fa0d52a1a8) (L 0x100000000000dfd9006d6d504f98cc2))) (N (L 0xfffffffffff8e1a871e9a0321a3168) (N (L 0x100000000000394a1dde3c8df39ba76) (L 0xfffffffffffe381974b8fdbf4d5a10)))) (N (N (L 0x1000000000000e042aa7e06ff3c709b) (N (L 0xffffffffffff92df33676ca75d470f) (L 0x1000000000000348af1dc55a14839d3))) (N (L 0xffffffffffffe6f6bc5a026b2f3fa3) (N (L 0x10000000000000bceebcb1710f11bc0) (L 0xfffffffffffffa7c78af48d5ad8245))))) (N (N (N (L 0x1000000000000028ca451983f22dd13) (N (L 0xfffffffffffffed5258f04722c0e1f) (L 0x100000000000000878dc992649b4309))) (N (L 0xffffffffffffffc31661d642736808) (N (L 0x1000000000000001b1f10cb56b233b2) (L 0xfffffffffffffff4086870d41e2136)))) (N (N (L 0x100000000000000053bd47d564dd1a6) (N (L 0xfffffffffffffffdbb2488e3d395ac) (L 0x10000000000000000f9a91e966142c6))) (N (L 0xffffffffffffffff9599190848a470) (N (L 0x100000000000000002cf85d3c5bd411) (L 0xffffffffffffffffed2632c8e52256)))))) (N (N (N (N (L 0x1000000000000000007d695b962564a) (N (L 0xfffffffffffffffffcc44938d5b786) (L 0x100000000000000000152c1b4a6b045))) (N (L 0xffffffffffffffffff766da91ac5b5) (N (L 0x100000000000000000037718aedd38a) (L 0xffffffffffffffffffe9d2ba6c754e)))) (N (N (L 0x100000000000000000008ce088af215) (N (L 0xfffffffffffffffffffc879ff35130) (L 0x1000000000000000000015b9bc91842))) (N (L 0xffffffffffffffffffff78f40f7c35) (N (L 0x1000000000000000000003418f52600) (L 0xffffffffffffffffffffec0a9ce621))))) (N (N (N (L 0x1000000000000000000000798023ae1) (N (L 0xfffffffffffffffffffffd2158c83f) (L 0x1000000000000000000000113c6df4b))) (N (L 0xffffffffffffffffffffff99291436) (N (L 0x100000000000000000000002619945d) (L 0xfffffffffffffffffffffff1f9c252)))) (N (N (L 0x1000000000000000000000005212489) (N (L 0xfffffffffffffffffffffffe22bba4) (L 0x1000000000000000000000000ac62ff))) (N (L 0xffffffffffffffffffffffffc21e02) (N (L 0x100000000000000000000000016145c) (L 0xfffffffffffffffffffffffff82b60)))))))

private def cneg_lf_65 : FastDTree := dleaf cneg_bt_65 0xfffffffffffbdc3e0cedaf8efa61b0 0x10000000000080638cb5e4f17162ee7 0x1000000000001cfe2e7c00bdaad1982 0xfffffffffffe874953d56cfed2f8c9 0x90779182254a121442f 0x25595377db2481b522b (M 0xfffffffffffbffd1af64ca900beff6 0x100000000000600484e286ae523d500 0x1000000000001af8f3d753204c030fb 0xfffffffffffecf0496d788b49548a4 0xfffffffffffbf66d952ca4a0081ebc 0x100000000001ccd4409d22ac95eb6f7 0x100000000001806ae675f43d481f049 0x100000000003653849aef625e5f52ec 0x21073227af9bc1070c4 (Q 0x73661041783fc836883 0x1d155b4d110706d4e6bf 0x3b66e7d0d9ddac597869)) (M 0xfffffffffffcc22eff041f7c8e8d62 0x10000000000032950f9a081ea70fd13 0x10000000000016be99c089e7add274c 0xffffffffffff3ba46ba51cc0d0646d 0xfffffffffff8b20efd05a41caad5b7 0x1000000000011542d05bd5a846ffc98 0x10000000000048ccb3aab661b75d7a4 0x1000000000025b69e61e4aa52621ca4 0x19d825559ccf6a25cf5 (Q 0x4872246d3c64f90dba7 0x12ce2ea0ce21d2d4c59a 0x25fca144b740e13686b8)) (M 0xfffffffffffdb048fdbe4934f18630 0x10000000000018221bd6070d4eb8ab3 0x10000000000012c12937f4646074a2b 0xffffffffffff8394bf3949149c800d 0xfffffffffff8c43e0747d58f6702de 0x1000000000009b0d7b98fb476f87e41 0xfffffffffffc383409751d3c9cedcd 0x100000000001808264b88871537424c 0x144d863954e832a5d19 (Q 0x2c28f3424a19f3da53e 0xc17bcff26e9a1803114 0x1853cec6bbb36cc822d7)) (M 0xfffffffffffe83f562b35dd1120f85 0x10000000000009dd9959a361c4402d1 0x1000000000000f4f3a092eebbc54d56 0xffffffffffffb15eff560d0147866e 0xfffffffffffa1b1632d5e40d3ef962 0x1000000000004fbd6199f6db9257dad 0xfffffffffff9b89d420862cba41d3c 0x100000000000e41703c8f9072fd2f2c 0x101436e6335a11467c4 (Q 0x19b85431795b625d5bc 0x7b8007575a25345d0af 0xf93be63d475474c77a6))

private def cneg_bt_67 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff7629a19dda0eb56aa7891) (L 0x100000000299b92437dbff55d67c0d1))) (N (L 0xffffffff6eaca01b22cbb4ac798b2d) (N (L 0x100000001969b4777bc6296454ad366) (L 0xfffffffc3dd81051b8b1129dd65e5d)))) (N (N (L 0x100000007c76114396491daa7bb2e7c) (N (L 0xfffffff1982b892bf0cf3e0dd6e112) (L 0x100000018438ed471ff09add041a9f4))) (N (L 0xffffffda5e711fee9b4db12d2196b5) (N (L 0x100000036418df75a9914a84ab54dfb) (L 0xffffffb6b828846ca5b2738c9210b1))))) (N (N (N (L 0x10000005d4ce9a92a23e831f0684dc5) (N (L 0xffffff8f705ed5b01a058d422e4583) (L 0x1000000813e2723e7a14faec037bbaf))) (N (L 0xffffff723c80d86b7b6de2296dbf40) (N (L 0x100000095074ac0ce65eb3e948d6392) (L 0xffffff696d7e85e25abf17dc9df070)))) (N (N (L 0x1000000929414bb2aa80af78253f79b) (N (L 0xffffff76373e861a1dac677adbfe06) (L 0x10000007d4f4974a1c9376b33cf0e12))) (N (L 0xffffff918b359f95e0f408e2afc63f) (N (L 0x10000005e84116fb71d5ceeb567180a) (L 0xffffffb16055f8d15c706aff869106)))))) (N (N (N (N (L 0x10000003faa61810ec7f6560c9f5f21) (N (L 0xffffffcdc1b9c74e67dc673aeb794c) (L 0x100000026af8801160ab6d79dddb812))) (N (L 0xffffffe2e8acdf24767fb258f644bd) (N (L 0x100000015629dd5f1c7e40d56f4a8af) (L 0xfffffff09e741c826d573e66405c8b)))) (N (N (L 0x10000000ad5187531ca707cb7741609) (N (L 0xfffffff886342daa1c75c848bb877c) (L 0x1000000050f2733ba2fac66e4c20355))) (N (L 0xfffffffca3f2d4b7b0eb6d15894993) (N (L 0x10000000230c09afdbb49c410b8a425) (L 0xfffffffe98d24418ced36fe5fc9ca5))))) (N (N (N (L 0x100000000e223d09ead2f4c79cba4b8) (N (L 0xffffffff73fab32d50f1e7167afc9d) (L 0x100000000554d925276d2f215ad63e8))) (N (L 0xffffffffccd83c6266f3426890c724) (N (L 0x1000000001e35e66fc8d8da2b4d9839) (L 0xffffffffee6c49eea4c85637fc0f8e)))) (N (N (L 0x1000000000a143925d81db78528aff3) (N (L 0xfffffffffa4d43dcfe941140cfbd57) (L 0x100000000032d619409cb8b00c6912c))) (N (L 0xfffffffffe4089e6a030ad90669280) (N (L 0x10000000000f2f09ecc7db28c8d179e) (L 0xffffffffff7dc95108514640b3faa8))))))) (N (N (N (N (N (L 0x1000000000044ebe239f23ed1cb71f3) (N (L 0xffffffffffdbf7477becc0cdec3a63) (L 0x10000000000129d49c87de3645d5f56))) (N (L 0xfffffffffff67f29d81ba705edfade) (N (L 0x1000000000004cbcf2c56607f51ad8d) (L 0xfffffffffffd9b4dbe7b9c8a27917a)))) (N (N (L 0x10000000000012e617a5792bfeee4af) (N (L 0xffffffffffff6c60af9f9d2a8ac492) (L 0x1000000000000474e7cb209412ef4b0))) (N (L 0xffffffffffffddea03699326a36cc6) (N (L 0x10000000000001020ad96e0f170184a) (L 0xfffffffffffff8721260184e4b7213))))) (N (N (N (L 0x10000000000000380f9ee2881931cfe) (N (L 0xfffffffffffffe63fd3d5ec0b9e955) (L 0x100000000000000bb7467d3ce7c06e6))) (N (L 0xffffffffffffffab8213f22b867e2b) (N (L 0x10000000000000025bbe7891ff46be1) (L 0xffffffffffffffef4ccd9e3bde22cc)))) (N (N (L 0x10000000000000007534ab44ed85637) (N (L 0xfffffffffffffffcd098715ad4a962) (L 0x100000000000000015f80c3489e4ff7))) (N (L 0xffffffffffffffff69c1bd3907acf2) (N (L 0x100000000000000003faefc1e8a42cb) (L 0xffffffffffffffffe53a5e2493c900)))))) (N (N (N (N (L 0x100000000000000000b29e9e462ecd7) (N (L 0xfffffffffffffffffb61c3dd67d28e) (L 0x1000000000000000001e5374a9efe34))) (N (L 0xffffffffffffffffff3a65d1994d72) (N (L 0x10000000000000000004fdbce6e38c8) (L 0xffffffffffffffffffdff80e6330e3)))) (N (N (L 0x10000000000000000000cc08e89742c) (N (L 0xfffffffffffffffffffaf5d57f7de0) (L 0x100000000000000000001fa31db0e87))) (N (L 0xffffffffffffffffffff3acfb5f63c) (N (L 0x1000000000000000000004c463ecfba) (L 0xffffffffffffffffffffe2b38ac685))))) (N (N (N (L 0x1000000000000000000000b2d5393ca) (N (L 0xfffffffffffffffffffffbc3d5e56c) (L 0x10000000000000000000001980b6c53))) (N (L 0xffffffffffffffffffffff6770a589) (N (L 0x1000000000000000000000038aab52a) (L 0xffffffffffffffffffffffeb16646b)))) (N (N (L 0x1000000000000000000000007ab1ec8) (N (L 0xfffffffffffffffffffffffd34ad37) (L 0x10000000000000000000000010306e2))) (N (L 0xffffffffffffffffffffffffa2c7e4) (N (L 0x10000000000000000000000002157fe) (L 0xfffffffffffffffffffffffff42521)))))))

private def cneg_lf_67 : FastDTree := dleaf cneg_bt_67 0xfffffffffffba639d7c5b31b73d117 0x1000000000007c362cfe5de0d8f51df 0x1000000000001bbfa7ff584ce14c98f 0xfffffffffffe9ad3a028e937392786 0x8e632e28d3eaa28caaf 0x239d11f34bedd6302d5 (M 0xfffffffffffbd4202ca80899f057e7 0x1000000000005c22858be8f57fd1e81 0x10000000000019c4e9dfa5d962d7d92 0xfffffffffffedf534ddf5a41a33ad3 0xfffffffffffb5fea08e06102bf5aee 0x100000000001c7f90f5fddbf021c38b 0x10000000000172576c817db35ce73c5 0x10000000000366d9b4b77996f5bae69 0x1f7520cc0be563a1410 (Q 0x71c4d7033206ebbde62 0x1cdf0857a60641bc6ff6 0x3b25386d4d620f49da04)) (M 0xfffffffffffca613eefa1cdf6a54b1 0x1000000000002f507b3019abfe3b0e9 0x10000000000015a4cdff4ed18013bd6 0xffffffffffff4674571ff75ff589db 0xfffffffffff84cd8c3de1f63de5c12 0x10000000000110664a61be10186e2e6 0x1000000000003e32ae6c12349a0a4de 0x1000000000025a218c6539cb37abe63 0x188e06daf3ebd4ed7a3 (Q 0x4782bdd9852d0a74ad7 0x12af69f4eb470e9a8c03 0x25d55c2e8557cd4d9879)) (M 0xfffffffffffd9e732455f81e32a080 0x1000000000001571b6133954ecad0ed 0x10000000000011c53973c3bfb86a281 0xffffffffffff8a0b332dbbd6fac5fc 0xfffffffffff8830fdc638a3281af80 0x10000000000096b5a258e2ecdf79aa3 0xfffffffffffbc01b84818c430503f0 0x1000000000017dda9a24639e19c1fe9 0x133d31e844f8a11b8f4 (Q 0x2bb7b82e2e4c67722e3 0xc0877a3a4ddd11b9bcd 0x183dc37a30bfae5d2124)) (M 0xfffffffffffe789d3ca1c0246fcaa7 0x10000000000007accbac6a488a0736d 0x1000000000000e71c70359c91d81bf0 0xffffffffffffb47207df787d451fb4 0xfffffffffff9f2c2e976fa8576d253 0x1000000000004c1fbd213c3a9a80cde 0xfffffffffff96819a25d455e3a3ace 0x100000000000e10d058786ea5a07888 0xf32623850c15ad8df8 (Q 0x19a33115746e81dabc5 0x7b2b158b2d3c657afb5 0xf88cad179e53655b28f))

private def cneg_bt_69 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff73ce720df3aa4f7dfb5b4) (L 0x1000000002ae31e6c316d7c26bef187))) (N (L 0xffffffff687400a491a19adc89e1d8) (N (L 0x100000001ac769a5887cd7d80a2a1b6) (L 0xfffffffc005e3efa2962d8650f3142)))) (N (N (L 0x100000008598e2fc7a91c06e97ef7c9) (N (L 0xfffffff0684364400441658fd4badc) (L 0x10000001a78bfa0f05de84443d733fc))) (N (L 0xffffffd6a2a5e766bbf1aa3fa14c28) (N (L 0x10000003c119162cdc0817aa8ba07d3) (L 0xffffffae4eea641e3920b71aab36e2))))) (N (N (N (L 0x100000068b3626250603fcdb525346f) (N (L 0xffffff80e006f4d4358bb6ca54984b) (L 0x100000092deda734c5c6b430ccfa3dc))) (N (L 0xffffff5deea06152a4a2deb606c770) (N (L 0x1000000ab5e3a5bbd06fb3a6301b1bf) (L 0xffffff51df8d67fa6d4e00373ecc72)))) (N (N (L 0x1000000aa722e72d422bd1522f02c88) (N (L 0xffffff5eea5e20a2a55338477696b0) (L 0x10000009345ca7cc1fffae29ebb2460))) (N (L 0xffffff7d83eddcb6cb9078bc33215b) (N (L 0x100000070378a1f056fd156a25b2d90) (L 0xffffffa230c68bdddcddc190833499)))))) (N (N (N (N (L 0x10000004c547bdc86acb0a51f462a75) (N (L 0xffffffc379e4c4e7cadad99ec30964) (L 0x10000002ed196068ffe90f928eae642))) (N (L 0xffffffdca1b5aa84f59196916ad68f) (N (L 0x10000001a1de341bcd09aac45c8ce1e) (L 0xffffffed21f70261406788e81cf449)))) (N (N (L 0x10000000d587971e1c58e13b011f1aa) (N (L 0xfffffff6c0122a0c027eaf403a8f88) (L 0x10000000649425f45a09cc673ed9acb))) (N (L 0xfffffffbcee9e599db63333f61950f) (N (L 0x100000002be862f2e0cbb795037d2ab) (L 0xfffffffe3c308bf25f0fbdac85d594))))) (N (N (N (L 0x1000000011d990fa873d05d456c1b05) (N (L 0xffffffff4e777d30cfebd77b81837e) (L 0x1000000006c93d6b301ff2b3c33778e))) (N (L 0xffffffffbea3037d48c3a78ba4e9c3) (N (L 0x10000000026bf772902976a9ac9eb22) (L 0xffffffffe95f04f13a3678275b080e)))) (N (N (L 0x1000000000d0623b07b0bbe4e6033d1) (N (L 0xfffffffff89c1e7632141f3eec6f66) (L 0x1000000000422bac67929eb22ec4fec))) (N (L 0xfffffffffdb7799e471dfa7a71274c) (N (L 0x100000000013e7bb8a9f729a3351b56) (L 0xffffffffff54b213aab3cbfe79c4d3))))))) (N (N (N (N (N (L 0x100000000005afc74ac20099c161929) (N (L 0xffffffffffd0441467574e5bf01f56) (L 0x1000000000018be15bae4396a455395))) (N (L 0xfffffffffff3534f86ccc2ece06241) (N (L 0x10000000000066b052c651f8367d561) (L 0xfffffffffffcc962fa20515f8ac6a8)))) (N (N (L 0x1000000000001975098feb22d336448) (N (L 0xffffffffffff38803812f025348c24) (L 0x100000000000060ad186b7b1544ec3e))) (N (L 0xffffffffffffd1a3940e71886a6bd4) (N (L 0x1000000000000160158df6fd827fefd) (L 0xfffffffffffff5a8f420a4c91d4a7f))))) (N (N (N (L 0x100000000000004cf903bf3f728c99c) (N (L 0xfffffffffffffdc88c9a4149d9eb9c) (L 0x10000000000000102f84781d407472b))) (N (L 0xffffffffffffff8aeaf781204c5735) (N (L 0x100000000000000347274b414c5cffe) (L 0xffffffffffffffe8b7fb2d957f98a7)))) (N (N (L 0x1000000000000000a3e207aa8bdf034) (N (L 0xfffffffffffffffb887c2b1737a450) (L 0x10000000000000001ee64a3b2892a5b))) (N (L 0xffffffffffffffff2c107d0f95cbc4) (N (L 0x100000000000000005a17e99c2d071a) (L 0xffffffffffffffffda043a27807ad2)))))) (N (N (N (N (L 0x100000000000000000fe254db444a72) (N (L 0xfffffffffffffffff9691a1efd4280) (L 0x1000000000000000002b64b3d58fc39))) (N (L 0xfffffffffffffffffee4759429a227) (N (L 0x100000000000000000072e89cac0db6) (L 0xffffffffffffffffffd1c8743e7501)))) (N (N (L 0x1000000000000000000127350fcdac3) (N (L 0xfffffffffffffffffff8b03a15c00f) (L 0x100000000000000000002e0619f69ec))) (N (L 0xfffffffffffffffffffee05e2bdd5a) (N (L 0x1000000000000000000006f8ea6db5b) (L 0xffffffffffffffffffffd508beb395))))) (N (N (N (L 0x100000000000000000000106f320a91) (N (L 0xfffffffffffffffffffff9c1ae3692) (L 0x100000000000000000000025b21e8ec))) (N (L 0xffffffffffffffffffffff1de9b12e) (N (L 0x10000000000000000000000543201c5) (L 0xffffffffffffffffffffffe0d9223d)))) (N (N (L 0x100000000000000000000000b73ce92) (N (L 0xfffffffffffffffffffffffbd0fb92) (L 0x100000000000000000000000184cfa3))) (N (L 0xffffffffffffffffffffffff73b88d) (N (L 0x1000000000000000000000000324d72) (L 0xffffffffffffffffffffffffee1225)))))))

private def cneg_lf_69 : FastDTree := dleaf cneg_bt_69 0xfffffffffffb72f8599dfb3b6032b0 0x1000000000007836ba083d12df18524 0x1000000000001a8ddcb741c9c62bf45 0xfffffffffffeacd1759457e2d2099e 0x8c8bd9dfc7dfb5deb17 0x21fa6d971ae8fdcefce (M 0xfffffffffffbaabaf1209440a19cf6 0x100000000000586d0456fc98fca4159 0x100000000000189c1f418baad36a5a7 0xfffffffffffeee43dddf9fb2019cf8 0xfffffffffffad06a40e7c62552b0f7 0x100000000001c3374f71ce96d2433a7 0x10000000000164a53ad9e96c9999de9 0x1000000000036856a7e67ad99fe2b74 0x1df8f317619bc2fce8c (Q 0x705d3b2db08b21f6343 0x1cac820648fe4f3e4488 0x3ae6d929d1626448fb31)) (M 0xfffffffffffc8b7bf42e76937978da 0x1000000000002c34c16763302b216c8 0x100000000000149342f7d54ca3a6099 0xffffffffffff5036a5a7ab039e7fbe 0xfffffffffff7ed3a8f0960d3973140 0x1000000000010ba9b84e7eb37ac2592 0x10000000000033ecfbdc5ea590f5cc3 0x10000000000258c88214b3fe223ed15 0x17532cc2f43467e44cd (Q 0x46c898aad3a5f4bdf34 0x12933cc6ac9528b14fc9 0x25b05e9aac0c25b688df)) (M 0xfffffffffffd8d814fab8b04c6d94d 0x10000000000012e5fded77de68f6d0d 0x10000000000010ce9a5a4b9a5b7fa1a 0xffffffffffff8fb63ac5ae691ed8fb 0xfffffffffff84643dff69154a7c207 0x1000000000009280127b18370e5eb3e 0xfffffffffffb4c6c81eb95c48a0d29 0x1000000000017b2feb177b504f88097 0x1236a8cd2307d48491c (Q 0x2b7a63a0e800d1ea3c6 0xbfae346eea971837d75 0x18293a308b6073914d71)) (M 0xfffffffffffe6dad5d0ea08e439a48 0x100000000000059c6430166fa9f821b 0x1000000000000d96d8384848e0acf13 0xffffffffffffb6ef8ad9c53dab8ff7 0xfffffffffff9cdd22082e741be8c43 0x10000000000048a3e74e80f02f1e123 0xfffffffffff91b2cb426aeb63cf941 0x100000000000de090929cf7312df1b2 0xe56081fb7ebdd3397e (Q 0x19c37ec3c81fba11b12 0x7ae69c6fe644d3ab826 0xf7ec768fed476eb0d63))

private def cneg_bt_71 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff7173427e0d45e9914f2d7) (L 0x1000000002c3037cdfdd887645004b2))) (N (L 0xffffffff620abc48a89e046b59a379) (N (L 0x100000001c340080b6b8058fae743e1) (L 0xfffffffbbf9b013c2c85fd479268a4)))) (N (N (L 0x100000008f5066763c4d2f4782e9972) (N (L 0xffffffef2226e0e9c5f95cca56d35f) (L 0x10000001cdc4fb0f90ec8206bfd31d0))) (N (L 0xffffffd2903fad45f5293a3641bbb8) (N (L 0x10000004274a0684975f5d6f12fd8c9) (L 0xffffffa4ffdfcea1fcf93764b4e1b7))))) (N (N (N (L 0x100000075679a0694c5d74fe1f2f14d) (N (L 0xffffff7089bea18e792a25421b7052) (L 0x1000000a6c56b2a3f0fe27912ac8ef7))) (N (L 0xffffff46de2d3186c1f035f0ee7ed7) (N (L 0x1000000c4e596c185d9dfb80871c1bb) (L 0xffffff36cc970be0fb54ab8da51aaa)))) (N (N (L 0x1000000c60921d7c740f4ecf46ce070) (N (L 0xffffff43d52c4b2167f1340610dcc9) (L 0x1000000acf045bee3cdac4707b240b7))) (N (L 0xffffff65fc9d9191e78814ecc1d54b) (N (L 0x1000000851e5423bc5da371a51bc17b) (L 0xffffff902b314651b00c1453b92321)))))) (N (N (N (N (L 0x10000005b6f0e1b5a0d6009848ce4cc) (N (L 0xffffffb727f424a661ac19ba01f1cf) (L 0x1000000389c8683b45047a1e02e1931))) (N (L 0xffffffd509cb62319781ae5918f705) (N (L 0x10000001fddd8bdb23522be2093e49f) (L 0xffffffe8e084027e80a1fb8d75c369)))) (N (N (L 0x1000000106d508c53384d3af5ad0129) (N (L 0xfffffff490d68567cf0b86648b130d) (L 0x100000007cdb7c93ee06df7d62099d3))) (N (L 0xfffffffac65684e1509c9f69153095) (N (L 0x1000000036f54230339d79a5cc59e78) (L 0xfffffffdc831a20026a25803311a6f))))) (N (N (N (L 0x100000001685aa5c9353c14149a892f) (N (L 0xffffffff1f1d3363725848ef8b35b8) (L 0x1000000008a12b4bd44820a1462b16a))) (N (L 0xffffffffac8fa5d499dc6470c28e37) (N (L 0x10000000031a6af8e75b06ff46895f1) (L 0xffffffffe2e517691749ed96a79600)))) (N (N (L 0x10000000010d0430ebc11cba62cfe20) (N (L 0xfffffffff66cb03c4554dfd02cef3d) (L 0x1000000000560c5ad7d4c567049144d))) (N (L 0xfffffffffd0528073fef36fa3b7935) (N (L 0x10000000001a11e0b43621b2ca73f8c) (L 0xffffffffff1edabc2083dca7646837))))))) (N (N (N (N (N (L 0x1000000000077ffc857ed8a499bdf71) (N (L 0xffffffffffc0d3fac4f6c66799ef03) (L 0x1000000000020db35421f58cf81c38a))) (N (L 0xffffffffffef1cbb648a74d80c15a1) (N (L 0x1000000000008948217c93dcf8eb0b3) (L 0xfffffffffffbb09fe74fc4b92dc5d5)))) (N (N (L 0x10000000000022420e99acf5c697c57) (N (L 0xfffffffffffef2a83f0fea890087dc) (L 0x100000000000082f18115cad2d70e06))) (N (L 0xffffffffffffc1015115c180b9449c) (N (L 0x10000000000001dfed3bca615cb018c) (L 0xfffffffffffff1dc729a6cd971a5f1))))) (N (N (N (L 0x1000000000000069949fc0e36ffada7) (N (L 0xfffffffffffffcf33d09fc6d5dce01) (L 0x100000000000001656a1036e8df138f))) (N (L 0xffffffffffffff5deaec3348e4cca2) (N (L 0x10000000000000048d31d67469b63fc) (L 0xffffffffffffffdf9372822148f0f9)))) (N (N (L 0x1000000000000000e4ebcb35e0f1174) (N (L 0xfffffffffffffff9bdf22bbab90c69) (L 0x10000000000000002b6acd717baae39))) (N (L 0xfffffffffffffffed556d399828daf) (N (L 0x100000000000000007f53f1a69fbc5b) (L 0xffffffffffffffffca29fa536ae12b)))))) (N (N (N (N (L 0x100000000000000001693e553c11e12) (N (L 0xfffffffffffffffff69b6ee7fa82cd) (L 0x1000000000000000003e0765cedf2d5))) (N (L 0xfffffffffffffffffe698e50f73d56) (N (L 0x1000000000000000000a52cdc4bee5d) (L 0xffffffffffffffffffbd61bcc9aa60)))) (N (N (L 0x10000000000000000001aab0109e687) (N (L 0xfffffffffffffffffff5672ea79d08) (L 0x1000000000000000000042e280641b3))) (N (L 0xfffffffffffffffffffe5cddf773b2) (N (L 0x100000000000000000000a2fecb264e) (L 0xffffffffffffffffffffc10e3fb658))))) (N (N (N (L 0x1000000000000000000001823d05491) (N (L 0xfffffffffffffffffffff6ce183fd3) (L 0x100000000000000000000037a952da8))) (N (L 0xfffffffffffffffffffffeb14a88c8) (N (L 0x100000000000000000000007cf81b0f) (L 0xffffffffffffffffffffffd1a49a34)))) (N (N (L 0x100000000000000000000001115ffa3) (N (L 0xfffffffffffffffffffffff9be1094) (L 0x1000000000000000000000002470622))) (N (L 0xffffffffffffffffffffffff2d1ede) (N (L 0x10000000000000000000000004bcf05) (L 0xffffffffffffffffffffffffe4e994)))))))

private def cneg_lf_71 : FastDTree := dleaf cneg_bt_71 0xfffffffffffb4243af0e9d086c4b08 0x100000000000746392b75a9e2c72550 0x10000000000019659bfdfe6afbd0e2f 0xfffffffffffebd801bc15d4a040070 0x8aed764e3456fc2b1b3 0x206c6926b0629082886 (M 0xfffffffffffb8372c42d3d5a5e0687 0x10000000000054e293d535304346756 0x100000000000177b9c2f1f53082f128 0xfffffffffffefc117607501ef94d48 0xfffffffffffa478863f79b401033bd 0x100000000001be8bbec6bc4d92479a6 0x100000000001574f97f9acb56a3643b 0x10000000000369af7a875008dbb681b 0x1c8e036afee9a49c3cc (Q 0x6f2b37850e7969b1062 0x1c7d4734738fb9ba31d1 0x3aab771e1ad08ffabb72)) (M 0xfffffffffffc72436fb181240738d9 0x1000000000002940dda824ab1579a87 0x10000000000013876c607659df088d6 0xffffffffffff5922f43645bfbc894d 0xfffffffffff792e0354ab95c983d7a 0x1000000000010709d48ae574fede484 0x10000000000029f77d7a3b4e16cf7ee 0x100000000002575e937d2654dd04b85 0x1623a95c56afec9e960 (Q 0x463f6caab80165befab 0x12793b4f55b30e204225 0x258d640b59abb502ada6)) (M 0xfffffffffffd7d596b17c6775b137d 0x100000000000107e562141dc8c24475 0x1000000000000fdb22b3bec73ed8c33 0xffffffffffff94ca9880735e6a2a40 0xfffffffffff80d9531bf42003bfdbb 0x1000000000008e69a06d742fef7c24e 0xfffffffffffadcee8f4148599ce8d3 0x1000000000017881c146f89169f40dd 0x1136b74943db481d7ff (Q 0x2b6b99945f891770ce4 0xbeea66e5876fa51cf86 0x1815fb04ba909769cc5e)) (M 0xfffffffffffe631375a12ba9111b01 0x10000000000003ac2859842e4377bdf 0x1000000000000cbc9f0602975ee1e20 0xffffffffffffb90a0950612fd8eb04 0xfffffffffff9ac0bf4b8a707fa03fb 0x1000000000004546e2e165ba3d5fa0f 0xfffffffffff8d1a6e29eb122846bbc 0x100000000000db0a37792de6dd93911 0xd7ca8e32d1473304b4 (Q 0x1a115bf9ff019d4e3fc 0x7aadf967af74bd8efdb 0xf758717723bd159c31b))

private def cneg_bt_73 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff6f1812ee26e183a4a2ffb) (L 0x1000000002d82de68e30117161afa4b))) (N (L 0xffffffff5b7001bc8f26b304738f44) (N (L 0x100000001dafec9d0962e96a6022bb7) (L 0xfffffffb7b6abef86d80012bcf573c)))) (N (N (L 0x1000000099a483f903757edbd5b62df) (N (L 0xffffffedc46e648241bfbc0c970adc) (L 0x10000001f719e5c0cc1ca8f4c0600e2))) (N (L 0xffffffce202b5632285087a47365b2) (N (L 0x10000004977ffc636c34e2019222028) (L 0xffffff9ab46a745510a6d5c4af53cc))))) (N (N (N (L 0x1000000838d0c000c7acc912c8dec2b) (N (L 0xffffff5e39cd94b70ff4afb5ccb8a9) (L 0x1000000bd3870df9598f968c9f341ec))) (N (L 0xffffff2cb05cca3b09aeac71abdf4f) (N (L 0x1000000e20bfbd7be0f9d8b23167ff2) (L 0xffffff17b466031a5189036b4e02e7)))) (N (N (L 0x1000000e5e6dc1a70ccafacd0307461) (N (L 0xffffff24611f757b4b9b00f45bebd3) (L 0x1000000cae827e23d6c4346f3369f3a))) (N (L 0xffffff4a5ea479b950e1aae5586481) (N (L 0x10000009dc7336e1ff96fffa12f4af4) (L 0xffffff7accb133f71d71a4e89bf48c)))))) (N (N (N (N (L 0x10000006d6e63ef119cd3dc42ba57f5) (N (L 0xffffffa8679e68cd41d91fa62ece74) (L 0x10000004464690fdadb16a0c59aaddc))) (N (L 0xffffffcbdc5a1d55fd471c52582098) (N (L 0x100000026d902c6b5631eb6a02666b1) (L 0xffffffe3afd37eae67591b8dad3655)))) (N (N (L 0x10000001433a2c077046769c760cab2) (N (L 0xfffffff1e0cd7acd084f112b679b5c) (L 0x100000009adb198d1d04b48957f4ea1))) (N (L 0xfffffff97e0d160118037c36e9c643) (N (L 0x1000000044b9ef9a9afb29b925ba6a6) (L 0xfffffffd371312d3ad604396afa92a))))) (N (N (N (L 0x100000001c64208d187390fa355d6ab) (N (L 0xfffffffee365355a23b5cb91d36d82) (L 0x100000000af6af87fa56f0aae794114))) (N (L 0xffffffff95961642a1322ac81744bf) (N (L 0x1000000003f900fbfe1f9a14d364859) (L 0xffffffffda99adf92ef86640f9c2a3)))) (N (N (L 0x10000000015af6b086d107a2ecb0526) (N (L 0xfffffffff39ad66e7cc7044e8b4a8b) (L 0x10000000006fca820969c27fe503cb7))) (N (L 0xfffffffffc1d62b3197f3e8b79a055) (N (L 0x1000000000221c700e6dd5f93485f28) (L 0xfffffffffed85fb3d437147deb1d74))))))) (N (N (N (N (N (L 0x100000000009e1ca4ebbea5672221dc) (N (L 0xffffffffffac7a4738f30cc8a38223) (L 0x100000000002b96b83a8940c2c85f7b))) (N (L 0xffffffffffe9852e238b58031b80b3) (N (L 0x100000000000b759c19194f628921d5) (L 0xfffffffffffa3978e102401b72e799)))) (N (N (L 0x1000000000002e0e816b7bc80ce63a0) (N (L 0xfffffffffffe94b73995de7d083274) (L 0x1000000000000b12f07d9a782364362))) (N (L 0xffffffffffffaa7ca7fce1ed2db49d) (N (L 0x100000000000028d8c63e1ce09c84d8) (L 0xffffffffffffecaf8181539629fdec))))) (N (N (N (L 0x1000000000000090adb3fc96e0aaa00) (N (L 0xfffffffffffffbceccae846752a60f) (L 0x100000000000001eccb7a07670f12fe))) (N (L 0xffffffffffffff1fd7ee1c9043467e) (N (L 0x1000000000000006505049c3d987766) (L 0xffffffffffffffd2e33aa67b61c9d6)))) (N (N (L 0x10000000000000013f73e24a12fcc0a) (N (L 0xfffffffffffffff73dc4a4f06e037f) (L 0x10000000000000003cf1efe12cb0df5))) (N (L 0xfffffffffffffffe5b8b89b632e0c1) (N (L 0x10000000000000000b3c57417c2c01c) (L 0xffffffffffffffffb3c588adc107ec)))))) (N (N (N (N (L 0x10000000000000000200f562bb84323) (N (L 0xfffffffffffffffff29fe0a1be5b0d) (L 0x10000000000000000058941c7f700e7))) (N (L 0xfffffffffffffffffdb9f6e80a3ce0) (N (L 0x1000000000000000000ed31240896d4) (L 0xffffffffffffffffffa0125c1b17aa)))) (N (N (L 0x10000000000000000002681afbd29d6) (N (L 0xfffffffffffffffffff0a8337fb2dd) (L 0x10000000000000000000611a5a9e42b))) (N (L 0xfffffffffffffffffffd9ddd481a55) (N (L 0x100000000000000000000ede8df7bbb) (L 0xffffffffffffffffffffa3e187fb10))))) (N (N (N (L 0x100000000000000000000236c1c934b) (N (L 0xfffffffffffffffffffff278d6c99c) (L 0x1000000000000000000000521b1413e))) (N (L 0xfffffffffffffffffffffe10fcdda7) (N (L 0x10000000000000000000000b94cb6f4) (L 0xffffffffffffffffffffffbb162677)))) (N (N (L 0x100000000000000000000001976f4a3) (N (L 0xfffffffffffffffffffffff6a669de) (L 0x1000000000000000000000003695a2e))) (N (L 0xfffffffffffffffffffffffec3501c) (N (L 0x1000000000000000000000000722174) (L 0xffffffffffffffffffffffffd71e20)))))))

private def cneg_lf_73 : FastDTree := dleaf cneg_bt_73 0xfffffffffffb13ef074d77fdc8d3ef 0x10000000000070bb7e290e3db21eac7 0x10000000000018448d0bc7d49072450 0xfffffffffffecd1d2fe10baa20e660 0x89843886fe3167770c4 0x1eeeb5afc330d5007e8 (M 0xfffffffffffb5e212ee67259328473 0x100000000000518226e4212b4c9b6a7 0x10000000000016613abb89f0637c7fd 0xffffffffffff08f7830dd6de2002de 0xfffffffffff9c4e365e838947cdd5c 0x100000000001b9f397f16d29f96fc09 0x1000000000014a5209c3f6dd372fa62 0x1000000000036ae4a7c474e63273f9e 0x1b3060e97e1c2ebf838 (Q 0x6e2af7d68a5b8f6237d 0x1c50e789957c27f8acd6 0x3a72c77432c021b8e0ee)) (M 0xfffffffffffc5a4ef9ae353a1d1b67 0x10000000000026741ca4e875bd027a8 0x100000000000127f84a8b2114d1d134 0xffffffffffff6170ea3f6f2f9c4581 0xfffffffffff73d7970b2e86e0658ef 0x1000000000010283ccecf5af429db12 0x100000000000204e4a6b7b00111a926 0x10000000000255e3b263291b1d7800e 0x14fc48c883621e1a419 (Q 0x45e2dcb4c7b59315267 0x12610a0dad2a1b824306 0x256c2fc3402aca9cb5f8)) (M 0xfffffffffffd6de9294c6ec9ffc282 0x1000000000000e3a64de5da85b8bb3a 0x1000000000000ee965e195a3824cd21 0xffffffffffff997ce383bf286a770a 0xfffffffffff7d8c2102eae629aa86d 0x1000000000008a6f8a9d3c9f7658b43 0xfffffffffffa716c06fa524fb55612 0x10000000000175cfac32ea8274602fe 0x103ade71187f3830841 (Q 0x2b85a5df4f449bc5e50 0xbe3774c8ac48a3fad8c 0x1803d56bfe11283e2b9e)) (M 0xfffffffffffe58c4a6098cf9af06de 0x10000000000001dc14678470dec636c 0x1000000000000be2003859271f938fb 0xffffffffffffbaf3a1bad62f645ea5 0xfffffffffff98d3afe654afa78ce99 0x1000000000004206133621dfaa91106 0xfffffffffff88b5ae7d75e091d452a 0x100000000000d80fde6676b1976e98a 0xca46bd443a6ee8d16d (Q 0x1a8470d32a24e12fc33 0x7a7d7bc1ab7ee11742b 0xf6ce3b4e604ed06f486))

private def cneg_bt_75 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff6cbce35e407d1db7f6d1e) (L 0x1000000002edb123ce0e72b3c1fd25e))) (N (L 0xffffffff54a2ffb56ca1685362642c) (N (L 0x100000001f3ba37ba5975086b182748) (L 0xfffffffb33a8cd778621046c269610)))) (N (N (L 0x10000000a49d78ed823741bd85371d0) (N (L 0xffffffec4d9f4efdc4863bd716349b) (L 0x1000000223c4152815c02fe860d7033))) (N (L 0xffffffc94ad2abfb0ebc931c5ae5b5) (N (L 0x1000000512a087e3d78b02b03397b5c) (L 0xffffff8f53e3b49412c1254added66))))) (N (N (N (L 0x1000000934aae3a513890d31f30a1bc) (N (L 0xffffff49b701418c872ec8e181cc28) (L 0x1000000d686869922414593a4c3e1cd))) (N (L 0xffffff0eff6ae5d1968ecb4d1439ad) (N (L 0x1000001034e2f6f87bcb1d83d441cbc) (L 0xfffffef405751bb2467806eab74437)))) (N (N (L 0x10000010aad6b89b0dbccdf00ed5ca9) (N (L 0xfffffeffe1542272d4d0549c13d180) (L 0x1000000eddea4ae435f9fe7a5327ab2))) (N (L 0xffffff29fb147c9f7a857a7d3fb18c) (N (L 0x1000000bad8d985b7c1a7211a2d4ac2) (L 0xffffff617ba37499e8f607c4263268)))))) (N (N (N (N (L 0x100000082dbb13ebe476aa6a223524a) (N (L 0xffffff96c1fa42db2a4b56d9c3d7d1) (L 0x1000000528d67624456b5d00d2bf596))) (N (L 0xffffffc0c74606387d6ab9c149a7e4) (N (L 0x10000002f50f6c7286483b90fa15887) (L 0xffffffdd5ccc3fe3f2075f41b53e44)))) (N (N (L 0x100000018d2500fcbe76eabc618202c) (N (L 0xffffffee930f04c34e8e197715d706) (L 0x10000000bfe366f929a972124a73b73))) (N (L 0xfffffff7e714845afe74735e4c443a) (N (L 0x1000000055dd9110cbbf1d0ed74e589) (L 0xfffffffc81af6bf96e81d3174eeb9e))))) (N (N (N (L 0x1000000023c1b07de04d5a6c4ee9f46) (N (L 0xfffffffe98268fa2bcba0651f05989) (L 0x100000000dea82afd786b62e05ff447))) (N (L 0xffffffff786955d2bc292fec3da216) (N (L 0x100000000514bdc994d55afd035df66) (L 0xffffffffcffca29904f069a70beea7)))) (N (N (L 0x1000000001bf1373a19daa2ce6f2116) (N (L 0xffffffffeff8497c5c4f1949772216) (L 0x100000000091191b3a3ecec1caa4215))) (N (L 0xfffffffffaf06cd2238f1e40b47180) (N (L 0x10000000002c971c73c567543300df8) (L 0xfffffffffe7c3302cceefa629cd804))))))) (N (N (N (N (N (L 0x10000000000d0217529532a3977bfbe) (N (L 0xffffffffff91ad5c7e9a383f01fb65) (L 0x1000000000039c5809006df672b9235))) (N (L 0xffffffffffe21af7dc28fa5f18c72f) (N (L 0x100000000000f4a4a8be58a939e5fa2) (L 0xfffffffffff844ae06b49f9fda2e71)))) (N (N (L 0x1000000000003ddbde4f05b202e8ac1) (N (L 0xfffffffffffe167c09ddd52440b036) (L 0x1000000000000ef851eaf6ad5ee96c1))) (N (L 0xffffffffffff8c084ac050f29e15f0) (N (L 0x10000000000003791cc739901598f3c) (L 0xffffffffffffe5a42b76d7cefad9bb))))) (N (N (N (L 0x10000000000000c60f9573a55e38d68) (N (L 0xfffffffffffffa3e45e75d420c3296) (L 0x100000000000002a6c968b5370477ba))) (N (L 0xfffffffffffffeca4d22a3531a641c) (N (L 0x1000000000000008bfe0c1d54b76ff8) (L 0xffffffffffffffc14bc4c5525ce5ca)))) (N (N (L 0x1000000000000001bd588f8bbbee774) (N (L 0xfffffffffffffff3c0e2a27a58bda9) (L 0x10000000000000005576d5d299f66a7))) (N (L 0xfffffffffffffffdb0abdf9d5b0777) (N (L 0x10000000000000000fd8ff6e46c5957) (L 0xffffffffffffffff942c4a5c581b54)))))) (N (N (N (N (L 0x100000000000000002d7aa024badbb6) (N (L 0xffffffffffffffffecf8e4c10cedff) (L 0x1000000000000000007e5d904ea8f7a))) (N (L 0xfffffffffffffffffcbf596404ed90) (N (L 0x100000000000000000154443761bc92) (L 0xffffffffffffffffff76013a4bc85e)))) (N (N (L 0x1000000000000000000378b7478421a) (N (L 0xffffffffffffffffffe9cecb95d24a) (L 0x100000000000000000008cd4d9825b2))) (N (L 0xfffffffffffffffffffc88b75b5fee) (N (L 0x1000000000000000000015ae79a6983) (L 0xffffffffffffffffffff7951f79455))))) (N (N (N (L 0x10000000000000000000033ecdc3f86) (N (L 0xffffffffffffffffffffec1e054503) (L 0x100000000000000000000078fda4682))) (N (L 0xfffffffffffffffffffffd24a73257) (N (L 0x100000000000000000000011279e8b0) (L 0xffffffffffffffffffffff99a8a53c)))) (N (N (L 0x1000000000000000000000025e9e0c3) (N (L 0xfffffffffffffffffffffff20b2fe8) (L 0x10000000000000000000000051aeb92))) (N (L 0xfffffffffffffffffffffffe24e712) (N (L 0x1000000000000000000000000aba630) (L 0xffffffffffffffffffffffffc25c64)))))))

private def cneg_lf_75 : FastDTree := dleaf cneg_bt_75 0xfffffffffffae7d68d3966aa075105 0x1000000000006d3d8cdbd3ca9a7496d 0x1000000000001729218b2fbd97c05e3 0xfffffffffffedbe4c9fa9317f47fb4 0x884c7a8fa2aed267f6f 0x1d7dba8f88ef8aa27e8 (M 0xfffffffffffb3aa86255f0b9843d88 0x1000000000004e4af2b272d7869429c 0x100000000000154b99ac78656ee8b50 0xffffffffffff152fddf96ef3f73fae 0xfffffffffff9481f3670e3970b037e 0x100000000001b56c849ede373fe5a72 0x1000000000013da85417b18617b904b 0x1000000000036bf6c99cf36adaeb0e2 0x19dcd39c2932f3200d2 (Q 0x6d58aec7f9c337d80eb 0x1c2701d61f78a790d81a 0x3a3c86d5cf35581036f3)) (M 0xfffffffffffc438b4179c2aa13bc46 0x10000000000023cdfffc6983551f0b3 0x100000000000117a80374824d48ada0 0xffffffffffff69567ab29721a70528 0xfffffffffff6ecba12156375b5b519 0x100000000000fe15366b5a19d0ba76f 0x10000000000016edae89f45ac236aac 0x1000000000025457f1491e2a3062743 0x13da8d7a634850139e4 (Q 0x45ae5cfec3531bf33d7 0x124a5bdda458050946bd 0x254c8c1c7a0538cedfb7)) (M 0xfffffffffffd5f25ddc15df97abe43 0x1000000000000c19f8e0eba917df8b7 0x1000000000000df8a779098cbce7297 0xffffffffffff9dffd9e9ab0bb36a63 0xfffffffffff7a78c0ed67c2fc610c1 0x100000000000868f6e4d3d5026e1249 0xfffffffffffa09b207b62ad6c36393 0x10000000000173195cc7d3faac55ca5 0xf41498e7864752c9bb (Q 0x2bc2883add77b4daaa2 0xbd9199528474a0039f1 0x17f29f7915dc8edc4b4d)) (M 0xfffffffffffe4ebd4e84bf7a11c168 0x100000000000002c41d02988af7aa93 0x1000000000000b0687f186ecb8ba0aa 0xffffffffffffbcdc72a855beee4f06 0xfffffffffff9712c8951596c0babf8 0x1000000000003edf322813b13c6c542 0xfffffffffff8481dc954011924ba00 0x100000000000d5196d04b6ed17f2b66 0xbcc0f17d42025183e7 (Q 0x1b145348bfe14baf152 0x7a523d6e83a8cc9bf09 0xf64bd358f9da023f8fb))

private def cneg_bt_77 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff6a61b3ce5a18b7cb4aa41) (L 0x1000000003038d349f78ac3d65e8ce4))) (N (L 0xffffffff4da2e4e86873e603b0e163) (N (L 0x1000000020d79c8ad29d9e42a895f6c) (L 0xfffffffae82f6ae01381937bbd5baf)))) (N (N (L 0x10000000b043da694d0194fcd23810c) (N (L 0xffffffeabc2b2f59f94b64f56da4b9) (L 0x100000025400779801e122eaa39d635))) (N (L 0xffffffc40814273d394c3949724a8e) (N (L 0x1000000599a3bbd4746ca512bc5c57c) (L 0xffffff82c3727b72a18768540cccb2))))) (N (N (N (L 0x1000000a4cb40d2f7ee3915e3a867ec) (N (L 0xffffff32c223e7cd918ddc45481ce9) (L 0x1000000f307233c4c80046eaee01f9a))) (N (L 0xfffffeed595bae2e78e59b1632a732) (N (L 0x10000012938d60db1263dd8ebefe5dd) (L 0xfffffecb1ab9d41f9125e42298b379)))) (N (N (L 0x10000013515b50eaf561697773a1457) (N (L 0xfffffed58f64016134467d12646aea) (L 0x100000116a03bf8d5fa20809c68c2d0))) (N (L 0xffffff0406f06658035bb714b091e6) (N (L 0x1000000dd15beedb35252e3e9138c55) (L 0xffffff4383da5913b1b139f019eea1)))))) (N (N (N (N (L 0x10000009c58b15b01addce892d3931f) (N (L 0xffffff81aa27e2933037f7c17effd5) (L 0x1000000638ec0b244dc96ec22d73c05))) (N (L 0xffffffb36855a7bf317703f5d33173) (N (L 0x10000003994888984a9bd6a2c60220a) (L 0xffffffd5a9ba6dacc99ee026c0ce41)))) (N (N (L 0x10000001e78809be21deb302ef6b94b) (N (L 0xffffffea84625bd24347231db32867) (L 0x10000000ed901e43342f2c9e5e02d7f))) (N (L 0xfffffff5ef054581e0e57638666fe8) (N (L 0x100000006b2e7c04de7ff9515a74bde) (L 0xfffffffb9f2ad1b3f3020e5f0149f1))))) (N (N (N (L 0x100000002cfde00925d4b92a82ed9f0) (N (L 0xfffffffe396e28cd0b30aefa7b561f) (L 0x1000000011a5b4d6c5206017eadc02e))) (N (L 0xffffffff5365d65bc01acf1cd3e6bd) (N (L 0x10000000067e18685c9c54bea1a4655) (L 0xffffffffc26b3bc6180c80fd10d29b)))) (N (N (L 0x10000000023f89494a36192a454e9b3) (N (L 0xffffffffeb49d23d2fe305e2848b9e) (L 0x1000000000bc26ca8d9dee15c469391))) (N (L 0xfffffffff969fcfc1dcdbdcb4ba8ea) (N (L 0x10000000003a3bd0424b03500262c27) (L 0xfffffffffe03c47a04c7971af5958a))))))) (N (N (N (N (N (L 0x1000000000111b6691aed82cf75ad63) (N (L 0xffffffffff6e6a7b3cb48ae027a8d6) (L 0x100000000004c7eedc30023651274e9))) (N (L 0xffffffffffd84861d43358d1c9677e) (N (L 0x100000000001461cb0fb27b64e500b3) (L 0xfffffffffff5a8d02046ac144e27a2)))) (N (N (L 0x1000000000005300b407047a17c82f2) (N (L 0xfffffffffffd6d075e1731ff8f5c5c) (L 0x100000000000143794a4e0e73fb3035))) (N (L 0xffffffffffff62e264eca2b4131a47) (N (L 0x10000000000004b868355d57dec40f7) (L 0xffffffffffffdc1018a1c3f5e1759d))))) (N (N (N (L 0x100000000000010ee0125a19fc4ab6a) (N (L 0xfffffffffffff81a3ec16d64d8bb00) (L 0x100000000000003a60f8dd4bab1c3d6))) (N (L 0xfffffffffffffe5488ce21e21f7f5b) (N (L 0x100000000000000c1cf5ca64048a68f) (L 0xffffffffffffffa8ee224dc6bd06c4)))) (N (N (L 0x10000000000000026c3d97a0101625e) (N (L 0xffffffffffffffeee4c60af347982d) (L 0x100000000000000077bab0c920ce52c))) (N (L 0xfffffffffffffffcc12d8432f6a6da) (N (L 0x100000000000000016549b4a4b063be) (L 0xffffffffffffffff67a0a016919ca9)))))) (N (N (N (N (L 0x1000000000000000040736025038f12) (N (L 0xffffffffffffffffe4f556123483a9) (L 0x100000000000000000b4179dcde19b2))) (N (L 0xfffffffffffffffffb5a03243c5cc0) (N (L 0x1000000000000000001e7a52b076db0) (L 0xffffffffffffffffff39b06fa36beb)))) (N (N (L 0x1000000000000000000500aa2545b68) (N (L 0xffffffffffffffffffdfeee60fca00) (L 0x10000000000000000000cc0c0b3835e))) (N (L 0xfffffffffffffffffffaf6f96188e5) (N (L 0x100000000000000000001f9532f03b2) (L 0xffffffffffffffffffff3b4b41b039))))) (N (N (N (L 0x1000000000000000000004c0a36b9dc) (N (L 0xffffffffffffffffffffe2ce9037fc) (L 0x1000000000000000000000b21c7d278))) (N (L 0xfffffffffffffffffffffbc8942ac2) (N (L 0x1000000000000000000000196284b83) (L 0xffffffffffffffffffffff682ba3a9)))) (N (N (L 0x1000000000000000000000038641d97) (N (L 0xffffffffffffffffffffffeb306c5b) (L 0x1000000000000000000000007a1bd31))) (N (L 0xfffffffffffffffffffffffd37facd) (N (L 0x100000000000000000000000101e460) (L 0xffffffffffffffffffffffffa3290c)))))))

private def cneg_lf_77 : FastDTree := dleaf cneg_bt_77 0xfffffffffffabddf0e3c8d151ed5db 0x10000000000069e8fc11767a1b15700 0x100000000000161284d79f79e1c3161 0xfffffffffffeea0fd60bbbdd9d9ef2 0x874295cf6cd68244f6e 0x1c1696f3f407fe49a1c (M 0xfffffffffffb18f2dcda338898626a 0x1000000000004b3c52f5b6f1aaaeae0 0x100000000000143a0c00f2188bf4ed0 0xffffffffffff20f12dd859d2cd4f14 0xfffffffffff8d0e4dada6947fd4055 0x100000000001b0f490a97a6c3a30c3b 0x100000000001314e772107019ba1489 0x1000000000036ce694314d752953c8b 0x1890da7cc36300a8486 (Q 0x6cb0764812f17ff9f87 0x1bff42746247983ea2e8 0x3a0878da62341c4e9d07)) (M 0xfffffffffffc2decaf5f88652106d1 0x100000000000214e23fa77adeb8a805 0x1000000000001077fd73fa59f6aa358 0xffffffffffff7106564aeea6dce871 0xfffffffffff6a05a207c621bc47f06 0x100000000000f9bc01543a09a61921a 0x1000000000000dd2292e30527f0606d 0x10000000000252bb7f064c802c615d2 0x12bca7e41dfc0614c16 (Q 0x459d274e64e749c730e 0x1234f0233cc4610a3abf 0x252e49e3f07b92c762a4)) (M 0xfffffffffffd510c1a4d9d4a00bc38 0x1000000000000a1cf09a3426f606e55 0x1000000000000d08cbbf21d84b3bfc7 0xffffffffffffa282e2d6b681dc8428 0xfffffffffff779b839dde955366fb9 0x10000000000082c73cdd1373fbd3a17 0xfffffffffff9a590675b34fecf4917 0x100000000001705ea144641ccce4504 0xe48c0799b16b59acbc (Q 0x2c1c0da9bec2dd61c18 0xbcf5c764c2ea5292bde 0x17e2352833cba2f9e455)) (M 0xfffffffffffe4500a8db1025739d13 0xffffffffffffe9ccfb0ad97d935fa2 0x1000000000000a2a5a89d7cfb4c194a 0xffffffffffffbef12bca9a51a02637 0xfffffffffff957b0babb827a0bc1a0 0x1000000000003bd046558f800784b90 0xfffffffffff807c6d091e1aee6787b 0x100000000000d2266fbf857207bd6a8 0xaf2d5e616899261785 (Q 0x1bb8de7e4187379474c 0x7a29ff89bfdb9452f6b 0xf5cf8e88c317c9e8e43))

private def cneg_sub_7 : FastDTree := (dsplit (dsplit (dsplit cneg_lf_63 cneg_lf_65) (dsplit cneg_lf_67 cneg_lf_69)) (dsplit (dsplit cneg_lf_71 cneg_lf_73) (dsplit cneg_lf_75 cneg_lf_77)))

private def cneg_node_8 : FastDTree := dsplit cneg_sub_6 cneg_sub_7

private def cneg_node_9 : FastDTree := dsplit cneg_node_5 cneg_node_8

private def cneg_node_10 : FastDTree := dsplit cneg_node_2 cneg_node_9

private theorem cneg_ok_0 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f true cneg_sub_0 0 3 = true := by
  decide

private theorem cneg_ok_1 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f true cneg_sub_1 1 3 = true := by
  decide

private theorem cneg_nok_2 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f true cneg_node_2 0 2 = true := by
  rw [show cneg_node_2 = dsplit cneg_sub_0 cneg_sub_1 from rfl]
  exact checkFastDTree_dsplit _ _ _ _ _ _ _ _ _ _ cneg_sub_0 cneg_sub_1 0 2 0 1 3 rfl rfl rfl cneg_ok_0 cneg_ok_1

private theorem cneg_ok_3 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f true cneg_sub_3 4 4 = true := by
  decide

private theorem cneg_ok_4 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f true cneg_sub_4 5 4 = true := by
  decide

private theorem cneg_nok_5 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f true cneg_node_5 2 3 = true := by
  rw [show cneg_node_5 = dsplit cneg_sub_3 cneg_sub_4 from rfl]
  exact checkFastDTree_dsplit _ _ _ _ _ _ _ _ _ _ cneg_sub_3 cneg_sub_4 2 3 4 5 4 rfl rfl rfl cneg_ok_3 cneg_ok_4

private theorem cneg_ok_6 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f true cneg_sub_6 6 4 = true := by
  decide

private theorem cneg_ok_7 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f true cneg_sub_7 7 4 = true := by
  decide

private theorem cneg_nok_8 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f true cneg_node_8 3 3 = true := by
  rw [show cneg_node_8 = dsplit cneg_sub_6 cneg_sub_7 from rfl]
  exact checkFastDTree_dsplit _ _ _ _ _ _ _ _ _ _ cneg_sub_6 cneg_sub_7 3 3 6 7 4 rfl rfl rfl cneg_ok_6 cneg_ok_7

private theorem cneg_nok_9 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f true cneg_node_9 1 2 = true := by
  rw [show cneg_node_9 = dsplit cneg_node_5 cneg_node_8 from rfl]
  exact checkFastDTree_dsplit _ _ _ _ _ _ _ _ _ _ cneg_node_5 cneg_node_8 1 2 2 3 3 rfl rfl rfl cneg_nok_5 cneg_nok_8

private theorem cneg_nok_10 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f true cneg_node_10 0 1 = true := by
  rw [show cneg_node_10 = dsplit cneg_node_2 cneg_node_9 from rfl]
  exact checkFastDTree_dsplit _ _ _ _ _ _ _ _ _ _ cneg_node_2 cneg_node_9 0 1 0 1 2 rfl rfl rfl cneg_nok_2 cneg_nok_9

end GaussSmallBridge

theorem solution (δ : ℝ) (hd_lo : -(1 / 2) ≤ δ) (hd_hi : δ ≤ 0) {t : ℝ}
    (hlo : -(23 / 16) ≤ t) (hhi : t ≤ -1) :
    ‖mellin (fun u : ℝ => (Real.exp (-u ^ 2 / 2) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ)))
      ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖mellin (fun u : ℝ => (Real.exp (-u ^ 2 / 2) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ)))
        ((1 / 2 : ℂ) - Complex.I)‖ := by
  apply GaussSmallBridge.sound_subtree_lit true GaussSmallBridge.cneg_node_10
    0 1 (by norm_num) GaussSmallBridge.cneg_nok_10 δ _ hlo hhi
  rw [abs_le]; norm_num [GaussSmallBridge.signB]; constructor <;> linarith

-- Prove2me | solution 1 for GaussianMellinBound.small_delta_p1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T03:33:07.09726+00:00
-- url     : https://prove2.me/submissions/72661d8a-5c15-4d4c-ac74-9bcbf60378ad

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

private def cneg_bt_154 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff1ca09241a727944918bce) (L 0x1000000006979301919f0b26b4dd7ee))) (N (L 0xfffffffde1bf4c4b9d80a9d6aecf23) (N (L 0x10000000873c6b379fa62c56d8d508c) (L 0xffffffe42a25d7da94b6ffad2358a8)))) (N (N (L 0x10000004e9b0158b28d17ed656780b4) (N (L 0xffffff3ca231ff98b8a4fe53647c51) (L 0x1000001b37863f7cc98de2523173dca))) (N (L 0xfffffc8d09291c42a20e0c0c1473cf) (N (L 0x10000066eaf94a11c3bb779da654f60) (L 0xfffff4de3c8d79cded9f10d9328fe2))))) (N (N (N (L 0x100001201cc7f1dad3948516e148c92) (N (L 0xffffe49bf06c169ce66ba2781ce0a2) (L 0x1000027611563e5a3714c067795e287))) (N (L 0xffffca4214a71bf11b754acfd1e80d) (N (L 0x1000045e20c3c2c3202be147864a589) (L 0xffffa92194a2b9614fa9511ff23703)))) (N (N (L 0x10000678601a7b9ce874d3ab80304af) (N (L 0xffff896c3006df505c20937d1f0104) (L 0x1000082d6eb3939e2d2cf38b001746a))) (N (L 0xffff74a432bcfb69435108896c6bfd) (N (L 0x100008f8b15e9d0499994b634c1d4b2) (L 0xffff70c7520f3ad76d202b700fd9ef)))))) (N (N (N (N (L 0x100008aa1ebfecac724cd2f5335aa91) (N (L 0xffff7da31c67109e9eee9350742435) (L 0x10000773d90908955c4cd48d0488487))) (N (L 0xffff95c94f4dcd37f17be9d5be5138) (N (L 0x100005c3bd6c1cc0dc426d2bbe2d9a4) (L 0xffffb1d70f22d9c6ab903f95435218)))) (N (N (L 0x1000040b1a6f99ed4b6ff10aab3a146) (N (L 0xffffcba6e0ed30533623d71ebac5f8) (L 0x1000029713bfebf01f2ab52349d0c75))) (N (L 0xffffdfe07dd5ef2e2dd7fcad9b6e89) (N (L 0x1000018657669f9d86bbcbc6544e05d) (L 0xffffedd59555fb30d7ec112d405014))))) (N (N (N (L 0x100000d45176e0243de60481782bdb9) (N (L 0xfffff67c13d902daebe8cee619fea2) (L 0x1000006b388423eb9cae4d12b0df0d6))) (N (L 0xfffffb5cc265e1f99a2fcf6e91dd36) (N (L 0x100000327c9224b3cadeca42bddb2b2) (L 0xfffffde3675e6dd158c4790db6687b)))) (N (N (L 0x1000001640248bda7c92bd895a6cfd1) (N (L 0xffffff193262a946775d6aaea2b05d) (L 0x1000000935cf61069026c9337ea142b))) (N (L 0xffffffa34d80f0125216eaf44341ca) (N (L 0x100000039780acd5e14b9995e90b575) (L 0xffffffdcdf9148331342b65d8f4dac))))))) (N (N (N (N (N (L 0x1000000152ccac82bbf4cfd51264007) (N (L 0xfffffff36835f24d4c0fe4269c1d90) (L 0x10000000763feb4b581a14d7e294fad))) (N (L 0xfffffffbb7e798ee31d84591eab82d) (N (L 0x1000000027301b13963ea53a5424079) (L 0xfffffffe9dc09e0675fc20d0cb289f)))) (N (N (L 0x100000000c5b9d6cc88432ad5da8951) (N (L 0xffffffff92f1b3fc0c6706a9390d30) (L 0x1000000003b73acf0448e027b73eec5))) (N (L 0xffffffffdff56577e2c7d5b0984837) (N (L 0x10000000011136caec459a10a1c7fe7) (L 0xfffffffff6ffd98a1455a976ad44e3))))) (N (N (N (L 0x10000000004b171a3f9027cac652edf) (N (L 0xfffffffffd94267d2154d6eac00006) (L 0x100000000013c7a06e50d2e6653d2be))) (N (L 0xffffffffff60101ecfb2f8904060f2) (N (L 0x1000000000050047dc8d2c4294a0089) (L 0xffffffffffd85c5ef906cafb23793b)))) (N (N (L 0x100000000001372471786c2711cb938) (N (L 0xfffffffffff68cfc54f291f8576586) (L 0x10000000000048c6bc22e35a5b1a7dd))) (N (L 0xfffffffffffdd4a8e31dd9e200529d) (N (L 0x10000000000010673a0bd161373a51e) (L 0xffffffffffff851312a909589ef8cc)))))) (N (N (N (N (L 0x100000000000039118b7112a88a7093) (N (L 0xffffffffffffe5bc40693e260aa1a6) (L 0x10000000000000bfc0ce9ad4145cd08))) (N (L 0xfffffffffffffa93d3028dd7c274d9) (N (L 0x1000000000000026ee37ffe1e11ffe9) (L 0xfffffffffffffeeac9b7ffc81436cc)))) (N (N (L 0x1000000000000007a607ff694de416f) (N (L 0xffffffffffffffca67c0c2f831b67d) (L 0x1000000000000001749a6e7cac41461))) (N (L 0xfffffffffffffff5f59ab07f9a2105) (N (L 0x100000000000000044bc88fe0574b04) (L 0xfffffffffffffffe2cfbcc7e854084))))) (N (N (N (L 0x10000000000000000c4d78c73446774) (N (L 0xffffffffffffffffada45a9021c678) (L 0x1000000000000000022356f422c7b03))) (N (L 0xfffffffffffffffff1e478ca19c3de) (N (L 0x1000000000000000005c6dbf3e431ef) (L 0xfffffffffffffffffda6a83448b338)))) (N (N (L 0x1000000000000000000f2d62cd5b051) (N (L 0xffffffffffffffffff9e9ac1c5745f) (L 0x100000000000000000026cccabbf406))) (N (L 0xfffffffffffffffffff0a55517977f) (N (L 0x100000000000000000006093ec6d9cb) (L 0xfffffffffffffffffffda478c9ce6c)))))))

private def cneg_lf_154 : FastDTree := dleaf cneg_bt_154 0xfffffffffff957dc398c0ee3cc0f2e 0x1000000000002b0a26d854a79853a06 0x1000000000000c3ca451107d33c500d 0x1000000000000186cd0f5b214567f22 0x72e04407ff76e1246f3 0xc54f10fed9d96f1646 (M 0xfffffffffffa4c4fb1140a6893d5df 0x100000000000147339d41aa8f08488d 0x1000000000000aba13bf9be37f79d30 0x100000000000029f53f9dc34a15608e 0xfffffffffff07213967d13511b9418 0x1000000000013000928c80d6da47bc7 0x10000000000009d30fcb427cc02ca7d 0x10000000000357b9d55832f96d17470 0xb0af6e3c5628829f8d (Q 0x5d7e9b5f5d6e4604f1f 0x188e0fe1dc831d65e33c 0x357c849461d86f18e25d)) (M 0xfffffffffffc2b075a38a0a16fd7c8 0xffffffffffff9f455c7c5eacbfd447 0x10000000000007fe8f37f970dd72698 0x10000000000003ceb850079bb3488be 0xfffffffffff226881474ab17031610 0x100000000000860d7e5f5436b5590b5 0xfffffffffff4141deedb8700fa3512 0x100000000002058dc311be7754e3449 0x8dad7e93913d9b1172 (Q 0x3d9bad51c5ac6e440e5 0x102fc16fbbea12f35a27 0x2279577c48e107676af1)) (M 0xfffffffffffdb0fc224f925b2cc695 0xfffffffffffefe25a9b481006b995a 0x10000000000005d188d10a505a9c6d2 0x1000000000000410a106c8702940f64 0xfffffffffff5933b4b87da2902d591 0x100000000000253dfefba56a434d984 0xfffffffffff1a2b1aad228514b5896 0x100000000001115250c0ce96d0e19db 0x7190ee8e16060363dc (Q 0x284d11539987ce79aa7 0xaae7bab9dea3c030c82 0x1651c122aba55b02b964)) (M 0xfffffffffffec6dbcb975099bb9609 0xfffffffffffee97d155dce42db3036 0x100000000000043d398ad43b3fc30cb 0x10000000000003cd798bb239af4214a 0xfffffffffff8f996bb355b647e4681 0xffffffffffff5ce2b3d442d0fafc33 0xfffffffffff392bcb686ed58752f4f 0x1000000000007794854036ea6aa73f2 0x5b1e2b41f7d3277b77 (Q 0x1a31440c714708d13d7 0x70dcb5699abbf289a90 0xe804a1bfb44d11fb833))

private def cneg_bt_156 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff1a4562b1c0c32e5c6c8f1) (L 0x1000000006b93b2bb79bfe2753ca5d9))) (N (L 0xfffffffdd20f7641327ce6292bd45d) (N (L 0x100000008c4c7dd7112290860202144) (L 0xffffffe2e591c2bc9c202cba11c62f)))) (N (N (L 0x100000052cc20542b52ed60864b9814) (N (L 0xffffff30c068e09ac4162594d61ae2) (L 0x1000001d11b8fd725f9f569528ab30f))) (N (L 0xfffffc4abf29c7a95ac4def01ecd1b) (N (L 0x1000006f58a5b198bdf727b4c492e92) (L 0xfffff3e1eeacc2bdc87b264e8faa3d))))) (N (N (N (L 0x1000013b7cb7c94915e2b9395edf286) (N (L 0xffffe1d54bc8cba57bbe1810653714) (L 0x100002b9d3a8d7e48400a453cae3457))) (N (L 0xffffc426f9d459cef7c7181576c847) (N (L 0x100004e3d33e9821a869df88c72820d) (L 0xffff9e3c5ea24282580d87308b4f35)))) (N (N (L 0x10000751a643aef91cd0505d12a4328) (N (L 0xffff793283bd433e2d1cf3866ebabc) (L 0x100009578bd5515c4bcd0c70a628762))) (N (L 0xffff6007f6392f03de72c9a71b32ce) (N (L 0x10000a58ca88cf658b9f55c1b17f41c) (L 0xffff5a0e9783fefc9246be4581d456)))))) (N (N (N (N (L 0x10000a15b5b17ef76f3e353a05e7c60) (N (L 0xffff6796f3fa6f88980bc72fb84eff) (L 0x100008c053449f589bcafa87a01b15c))) (N (L 0xffff82bc8e02cdb331a84354425dd2) (N (L 0x100006d3d7833c04532d470a1b62c5d) (L 0xffffa30a2d0106ff509563cb73cc4f)))) (N (N (L 0x100004d4353c749d16f8079f7bbc29f) (N (L 0xffffc139e5aa98d735095d57a5ac9c) (L 0x1000031e56b98276f28426b333153e5))) (N (L 0xffffd92b9f5152e0c1a694bd5aa008) (N (L 0x100001d9afae79fca09d37bc853c09c) (L 0xffffe9dec692d0732ab9d8ec293e6f))))) (N (N (N (L 0x10000103a3c1b7a06407d6342bee4d9) (N (L 0xfffff451e5e6c56a05ff065baff28c) (L 0x100000841b05966de6fb348e18a643d))) (N (L 0xfffffa43cf7eba3360cd81a6510b3c) (N (L 0x1000003ea96bc88b10b232b8e09cbed) (L 0xfffffd5e9c7fa1031f55e19c77f456)))) (N (N (L 0x1000001bd0b4db2a812f8992d0ee4ed) (N (L 0xfffffede74474ba9840380fbe73f4e) (L 0x1000000b98426506fbf1407c5d0b3cf))) (N (L 0xffffff8ae607c2240a25fecbb929e2) (N (L 0x100000048d904ac67874e2a1c72d1b1) (L 0xffffffd3526fe99c0e7f2212e93864))))))) (N (N (N (N (N (L 0x10000001b05f75bee6592844ee3483c) (N (L 0xffffffefe01bff317b9346c1d539b5) (L 0x1000000097e9a9d9ffbee43986e7bcd))) (N (L 0xfffffffa7b4263f8ed67394287266b) (N (L 0x1000000032ac334a4da701cf3efcca8) (L 0xfffffffe3475a612f3b888c293d91b)))) (N (N (L 0x1000000010150759d754e32394aa46e) (N (L 0xffffffff71a10e70656551f6dd114d) (L 0x1000000004ddb6ba1823f02e81299a1))) (N (L 0xffffffffd5e89417a16d608d2f1937) (N (L 0x10000000016804abeb7020f33f3a439) (L 0xfffffffff41a7c0a879add487d68d0))))) (N (N (N (L 0x1000000000638d6b519cf3e0f5dea73) (N (L 0xfffffffffcc7be0e7826d370f8ff65) (L 0x10000000001a619f70d22ef5bb8ca0e))) (N (L 0xffffffffff2a0cb1c11dcdd3757eda) (N (L 0x100000000006b5b4d8d06697e908334) (L 0xffffffffffcaa967b500a80a09e4c3)))) (N (N (L 0x100000000001a3e3b0a8a0d8ecb1b73) (N (L 0xfffffffffff336167daf2e1c515f66) (L 0x10000000000062c7518360126d4027b))) (N (L 0xfffffffffffd0c181281cc75edf032) (N (L 0x1000000000001663fda871bff226c97) (L 0xffffffffffff57bbc786ec21770959)))))) (N (N (N (N (L 0x10000000000004e56224fb0c5d4bd1c) (N (L 0xffffffffffffdbd8dedd91c9b4eb78) (L 0x1000000000000108ac4e21b815fa12d))) (N (L 0xfffffffffffff87ead47eda7aeb536) (N (L 0x10000000000000360773960f86139fc) (L 0xfffffffffffffe7e3bfb1422d4d08a)))) (N (N (L 0x100000000000000aac1c48ab6f76520) (N (L 0xffffffffffffffb5047127fb9f3e2f) (L 0x10000000000000020aaefa2d91c85ea))) (N (L 0xfffffffffffffff1e0bf04205f86b4) (N (L 0x100000000000000060ee8736f9dbbf0) (L 0xfffffffffffffffd6bb1eb6844f9cb))))) (N (N (N (L 0x100000000000000011708bff776a0ad) (N (L 0xffffffffffffffff8af38c366e0905) (L 0x1000000000000000030be360d37e6b8))) (N (L 0xffffffffffffffffebd8e2a4687c58) (N (L 0x100000000000000000845f0cff8ce06) (L 0xfffffffffffffffffca09c9d7e36cc)))) (N (N (L 0x10000000000000000015d88aa1aed88) (N (L 0xffffffffffffffffff7375cf88bb84) (L 0x1000000000000000000382082bf6f7d))) (N (L 0xffffffffffffffffffe9bbeaf43a73) (N (L 0x100000000000000000008c65e8e7a92) (L 0xfffffffffffffffffffc907b4b43e5)))))))

private def cneg_lf_156 : FastDTree := dleaf cneg_bt_156 0xfffffffffff95b292ff99826a66968 0x100000000000293d53aa59ec97773cb 0x1000000000000c338fda693c295128b 0x1000000000000145641d3dd174f910a 0x72057e41414960697dc 0xc447b5a6465bfd944c (M 0xfffffffffffa522860ae31549dd912 0x10000000000012df2519e1bba39aaea 0x1000000000000ab37b91ea89eee0690 0x10000000000002561d8e21618635b50 0xfffffffffff05074c21cda89cab058 0x1000000000012c89789806688bbeac4 0x10000000000003231541f8683985f40 0x100000000003561b75de46feec02643 0xaf408f07b4aa260e6f (Q 0x5ccde2affdb4689eb37 0x1878c183568f06446f05 0x3561cf36f66618f3ddd5)) (M 0xfffffffffffc339cd17aa3cd87c2b4 0xffffffffffff8c6d0f206eeab25102 0x10000000000007fe16db44116154bb4 0x1000000000000379a6f73865d5ae410 0xfffffffffff21ac08d4ed32603cd17 0x10000000000083271980fe26a4fd65f 0xfffffffffff3cf7309b50043b72148 0x10000000000202d9409d6dc548cb08c 0x8b727c45eb6f4d1d31 (Q 0x3d33b95a5673fd63129 0x10221243e1c194e838eb 0x2268d578fa8b03a802a4)) (M 0xfffffffffffdba23d38d026fb3cb8f 0xfffffffffffef0661e641cc442765e 0x10000000000005d799ca48327e43424 0x10000000000003b3ef4664a05f60dca 0xfffffffffff594972c5f99bcc130a3 0x100000000000230d1585e0b1c97b47b 0xfffffffffff17cc1b2af528d322b95 0x1000000000010e7913723f522f36f24 0x6eaba661e58629726b (Q 0x28221151473c0d87d89 0xaa5ba82fa47057dd58e 0x164795e1ae563c5c45c0)) (M 0xfffffffffffecf60099e3da36bc177 0xfffffffffffedf6f06d2d7ff644249 0x100000000000044959ff42bd583f22a 0x100000000000036c675e025514ad430 0xfffffffffff9018c0256014eaf1317 0xffffffffffff449a669602657d0dcc 0xfffffffffff382627bd3d914efdc6d 0x100000000000751897632fe983a21da 0x57c652770c5c8a0601 (Q 0x1a39ac32cab4d3f0732 0x7083bfe61009043ef06 0xe7a0fd3a82cd0717aa0))

private def cneg_bt_158 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff17ea3321da5ec86fc0614) (L 0x1000000006db3c296f24c96f3655637))) (N (L 0xfffffffdc20fea3548ba655100a2b7) (N (L 0x100000009181e44cf0fc3156646face) (L 0xffffffe194e40c20fab506fe481937)))) (N (N (L 0x1000000572deea203407383db616ca4) (N (L 0xffffff243d07f4f5bae35c1c2e4d66) (L 0x1000001f08a7bc31a28670caa212313))) (N (L 0xfffffc03f64d7f46c6d999a74f9d1f) (N (L 0x1000007867c13f7df8e2cc1710bcb65) (L 0xfffff2d108cb15678e15db3fb2f4cd))))) (N (N (N (L 0x10000159471a31c0a5f905b0d4bbdf1) (N (L 0xffffdecb580504ab0dcc411f418ecc) (L 0x100003046e93201c0b7b65722b92c5b))) (N (L 0xffffbd64461bb4d1cfead6ef0763f3) (N (L 0x10000578aafb729d001d894dd0974cb) (L 0xffff920a9a20a82089d4481cf5dcd7)))) (N (N (L 0x1000084619208acffc8f7812f08d62a) (N (L 0xffff66d97cfa0596f9f7adfd34588e) (L 0x10000aaa576154e719900bf808ae6d3))) (N (L 0xffff487e5dd459a15bcb0b9bed9631) (N (L 0x10000becd38a330cc62cf5c9a5c82a0) (L 0xffff3fdc6b14098115be0bc3b3b13c)))))) (N (N (N (N (L 0x10000bbad5cfff54f03f620e74c4e10) (N (L 0xffff4defee6c970ae42a76a204aa66) (L 0x10000a44e4d92aa0972a910bbd26147))) (N (L 0xffff6c6001207d9ba9fcf9595ab3cb) (N (L 0x10000814a1080521caa3b79324d70a7) (L 0xffff918457ccebc50d620a8d9dd6a7)))) (N (N (L 0x100005c34df1418a6843bbceabc8994) (N (L 0xffffb4c793257a0bbc9f4444f42070) (L 0x100003c07a3fa40f589a293ba5c71e9))) (N (L 0xffffd119522e6108d64285fe4388ba) (N (L 0x1000023e647a1a7a514df873bbe5378) (L 0xffffe50fc4e339c1461670e4420967))))) (N (N (N (L 0x1000013d43cf212fb7c57dafe96c629) (N (L 0xfffff1ac78c079e6a17fefaf08ed22) (L 0x100000a2a3b7058bab77ebbab67a87e))) (N (L 0xfffff8e9cbacc2a66d061d6805c0f9) (N (L 0x1000004db6489e821d8c26f2b355382) (L 0xfffffcb9dcb5d173ec16b0e2714a31)))) (N (N (L 0x10000022be7957ef59b5ac3c94818ff) (N (L 0xfffffe950cfff8c44b58f209aa1958) (L 0x1000000e95c248c34b5fe14ba595929))) (N (L 0xffffff6c30552cc7c1935510be9824) (N (L 0x10000005c44635ef90114d4208f630d) (L 0xffffffc7384a5a02accfe83d1c0c14))))))) (N (N (N (N (N (L 0x100000022756e1cb8d8bb5ef79bcd09) (N (L 0xffffffeb5ecb5f0cbaf7278efad386) (L 0x10000000c2ff81dfba698f37bcc46ce))) (N (L 0xfffffff8e4a599c4dfa6211a27099b) (N (L 0x100000004178021328fbe5fa9043b31) (L 0xfffffffdac5e2334dd3ca3606b1f2a)))) (N (N (L 0x1000000014e94966eaa562b7166c926) (N (L 0xffffffff464aff4840513abf8e052a) (L 0x10000000065dfd6357d8d5a88afdd51))) (N (L 0xffffffffc8c0bf0a55f571ffff4f1e) (N (L 0x1000000001d9ffb8559d30cbd196f56) (L 0xfffffffff04a02a09478c072b55381))))) (N (N (N (L 0x100000000083def5c3f280434bb22cc) (N (L 0xfffffffffbb8dd9bb1d9827de132ea) (L 0x10000000002327eba111c021b221641))) (N (L 0xfffffffffee20aa4ad402e639beac3) (N (L 0x100000000008fe97f59313d23d7d435) (L 0xffffffffffb84a5e7f9041a9f58a89)))) (N (N (L 0x1000000000023626fd35716ff1aed8c) (N (L 0xffffffffffeeb4ec0a7c3a854765dc) (L 0x10000000000085f443b7e6054a16ce2))) (N (L 0xfffffffffffbfbfe3e3137cc66b22f) (N (L 0x1000000000001e895d502efb1350ad9) (L 0xffffffffffff19df034d55f4cda4fc)))))) (N (N (N (N (L 0x10000000000006b6f81440fdd1b1f05) (N (L 0xffffffffffffce47b98d9e392fd14b) (L 0x100000000000016cffd813c24b3ef76))) (N (L 0xfffffffffffff59f20b52a0fba54ad) (N (L 0x100000000000004aeaac7cbdb50d197) (L 0xfffffffffffffde7a68e75409860da)))) (N (N (L 0x100000000000000ee0ce19bc76722fa) (N (L 0xffffffffffffff9730268119e78f97) (L 0x1000000000000002dc8e830029cf691))) (N (L 0xffffffffffffffec27b9e65e14cd6a) (N (L 0x10000000000000008891ca2a4cec4fb) (L 0xfffffffffffffffc5b401aa28db800))))) (N (N (N (L 0x100000000000000018b30466356a275) (N (L 0xffffffffffffffff59cc8c0af666fe) (L 0x100000000000000004563b5904fff35))) (N (L 0xffffffffffffffffe33cd59d063ccb) (N (L 0x100000000000000000bd66febf82140) (L 0xfffffffffffffffffb29818ec490ef)))) (N (N (L 0x1000000000000000001f6a6ef70641d) (N (L 0xffffffffffffffffff3563a79ff9e0) (L 0x1000000000000000000511e0f426ab3))) (N (L 0xffffffffffffffffffdfbd93484ae3) (N (L 0x10000000000000000000cbe9cfff26a) (L 0xfffffffffffffffffffaff765ac239)))))))

private def cneg_lf_158 : FastDTree := dleaf cneg_bt_158 0xfffffffffff95dd5ad8f9bf9d81010 0x1000000000002772e4c0217c3751632 0x1000000000000c1c18a251257576eae 0x10000000000000fefeee746c5c8cb76 0x713aba8ea68d018a550 0xc2695279d29ad2465b (M 0xfffffffffffa574e9012531c7b62ce 0x100000000000114d15fbcbd5025e342 0x1000000000000a9e8db5a65286411e1 0x100000000000020837580f7104811e4 0xfffffffffff02fddca099de3a8d1d9 0x1000000000012918e32f89336411151 0xffffffffffffc8b19b896eeb382ecc 0x1000000000035474db6ca7d923d277f 0xacfe5e568f948abfb8 (Q 0x5c2e78c58945fc4af71 0x1863b1361b6caf958fc2 0x35476aaba3632d5c642e)) (M 0xfffffffffffc3b6475a182fca47ab3 0xffffffffffff79a69f7e8be7211f64 0x10000000000007ef54fccbc4908f2d0 0x100000000000032068a95973abd1db9 0xfffffffffff20fa93700e111e185ea 0x100000000000804865b4e55581c36ce 0xfffffffffff38c0376d7d1f2674e11 0x10000000000200231edca4f51f95c40 0x8875ba9cbf23fcf49d (Q 0x3cdeb72ae93e3c116ff 0x10148a93b66a0e9db9fc 0x225880d092e869f250e8)) (M 0xfffffffffffdc26c35e910349e8edd 0xfffffffffffee2a90a1413bb43b926 0x10000000000005cf61b37626fee5523 0x100000000000035378d465fb16dc98d 0xfffffffffff5965db0e1b38c0bc82b 0x10000000000020e3b64a6f8fba9c327 0xfffffffffff157c2f72f220e67e0ff 0x1000000000010ba24b7f6d0c79a7525 0x6b1e111103a0ab9024 (Q 0x280a22ff55222f1f8b5 0xa9d14d39ce0d8cdefc2 0x163d82ac8f7d46b96be9)) (M 0xfffffffffffed6fb0a875a1513de9a 0xfffffffffffed5552e2b98958bbc90 0x10000000000004472c5f16af7bc4501 0x1000000000000307e2326c9cbf66346 0xfffffffffff909b8692e60633d7449 0xffffffffffff2cbc219fa13b37fc82 0xfffffffffff372b49f0ddfff52f943 0x10000000000072a13a2e6b2f5663ecd 0x53e2f2781c5f48fda5 (Q 0x1a53790b443ea293541 0x702c223f24805271660 0xe73e127e5422f7acf04))

private def cneg_bt_160 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff158f0391f3fa628314338) (L 0x1000000006fd95fab8396cfe5c7e903))) (N (L 0xfffffffdb1bfd6dd079ee8f9b7f969) (N (L 0x1000000096dd5b60550893124bae3df) (L 0xffffffe037c3e2990cc11936593561)))) (N (N (L 0x10000005bc23af0e1c41b946d1f6b41) (N (L 0xffffff1710c1f43cb1568b8eb9c1b7) (L 0x100000211dd7c720ef4720522b0c0d8))) (N (L 0xfffffbb86918d6e72396813f0e490c) (N (L 0x100000822334c33c7edf971daf60dc3) (L 0xfffff1aa01cf954b505738959afd89))))) (N (N (N (L 0x10000179ae3f184ea0a4ed336b9f22f) (N (L 0xffffdb7829620acd50a70b26d7d36a) (L 0x10000356878f65864b7a189c95b4de7))) (N (L 0xffffb5e917d489a25cd2fc753ae451) (N (L 0x1000061e4675644cb4583356b1f11ab) (L 0xffff8466b70db6e6d33a23b0db969d)))) (N (N (L 0x10000958f3c370b8b9eb6b4538b4f12) (N (L 0xffff521d57668a71c796f99a865831) (L 0x10000c2b1fee24a1654043e2e548998))) (N (L 0xffff2da16df72caae34f0697ec70f1) (N (L 0x10000dbc27b64ec5837bf6d62eac714) (L 0xffff21adf196e11a48b4e627233a9d)))))) (N (N (N (N (L 0x10000da245922560a56aff557185cfa) (N (L 0xffff301c60e84743443971a0fdd7f8) (L 0x10000c0ab3c63b609e74455c52807d1))) (N (L 0xffff5224fb81038d8121ab2225e798) (N (L 0x1000098e8b67967a8f6a8e1fb25438b) (L 0xffff7cc928e0875b61097da1a28855)))) (N (N (L 0x100006df5d5aeb31d6b522eea4864c2) (N (L 0xffffa5ee6819bc4eabc04975c5b05b) (L 0x10000482b0ec69e577eb43c473a5bbc))) (N (L 0xffffc7645006544b6964a6f6169b2f) (N (L 0x100002b7fc538b69a0994bc00f54dc9) (L 0xffffdf3ba0e418f6f4cec2321d819a))))) (N (N (N (L 0x10000183625602e101c325e87d3dd19) (N (L 0xffffee7105863273203838eb52e09c) (L 0x100000c81385aa861d72e302d1bce4d))) (N (L 0xfffff73ff9bc777962140fd40032ac) (N (L 0x100000604d406800e7872e4b6963696) (L 0xfffffbeda03e6d5c8d5446897ed7d1)))) (N (N (L 0x1000002b5d4e4b1f1a738545c46646f) (N (L 0xfffffe39667167ceefbce9dfd3056b) (L 0x1000001254ed19bb290f63d784f2ab3))) (N (L 0xffffff45933ec0f5b8734ced2cef2d) (N (L 0x100000074c4e0ad8b8629905ea3d69c) (L 0xffffffb7e5e659bdca862460dd8fc7))))))) (N (N (N (N (N (L 0x10000002be779727fdceef29d483057) (N (L 0xffffffe5a0c539747a8e127c75d5c9) (L 0x10000000fa1908bbce802b1beb75462))) (N (L 0xfffffff6daef48a7ed6070a9505589) (N (L 0x100000005483eb6beb4340991bb9ccc) (L 0xfffffffcfc9d1e7df002b7336de2ed)))) (N (N (L 0x100000001b2af70d5423ee4dce8e9f7) (N (L 0xffffffff0df7e72ac268fc5314b099) (L 0x10000000085304263edc15277998ace))) (N (L 0xffffffffb78bf1a81d2f3a632c075f) (N (L 0x10000000026f89bc59301cbd5c9ac18) (L 0xffffffffeb44f4b4b3f66beec563b4))))) (N (N (N (L 0x1000000000ae885ecc86d209f0e6ba9) (N (L 0xfffffffffa52363a8092349cb66887) (L 0x10000000002ecf164846f318869149d))) (N (L 0xfffffffffe8220550f2ae01831b112) (N (L 0x10000000000c0bfb14c6fc1e98a0ea0) (L 0xffffffffff9facc65d6cf10d3f4422)))) (N (N (L 0x100000000002fab40700912e1f06b2c) (N (L 0xffffffffffe8a2c5e9493ee1a62307) (L 0x100000000000b57f75569fb999f8b00))) (N (L 0xfffffffffffa8b2a1ac6c2d9ff46fe) (N (L 0x100000000000299c1a17c9fe901d75e) (L 0xfffffffffffec58a8f625a79acdda7)))))) (N (N (N (N (L 0x10000000000009336e67eb8f4f13883) (N (L 0xffffffffffffbbaea33da8fc109348) (L 0x10000000000001f6e92e5d457557d0a))) (N (L 0xfffffffffffff1a93c32c4de41aab4) (N (L 0x1000000000000067c98c79a19c38f8b) (L 0xfffffffffffffd16f2f8e64cdeb9b8)))) (N (N (L 0x1000000000000014b915e970d57d02c) (N (L 0xffffffffffffff6d9f7c26fab22dab) (L 0x100000000000000401c84db63e2f932))) (N (L 0xffffffffffffffe4236d2cf6d9edca) (N (L 0x1000000000000000c03e4dc6b37daa1) (L 0xfffffffffffffffadb942d3ddbeced))))) (N (N (N (L 0x100000000000000022f30d17f9ea7f5) (N (L 0xffffffffffffffff1438148e50d39b) (L 0x1000000000000000062b12a3c111631))) (N (L 0xffffffffffffffffd6fcb2c86e924e) (N (L 0x1000000000000000010ec240a6866c8) (L 0xfffffffffffffffff9110c2838e4f3)))) (N (N (L 0x1000000000000000002d23018872396) (N (L 0xfffffffffffffffffedc2ba0e3282a) (L 0x10000000000000000007520b0f0c816))) (N (L 0xffffffffffffffffffd14dedee1049) (N (L 0x1000000000000000000127e420abd9d) (L 0xfffffffffffffffffff8b94ed203e1)))))))

private def cneg_lf_160 : FastDTree := dleaf cneg_bt_160 0xfffffffffff95fd8d5ff575dd28917 0x10000000000025acfd6d2d5067046fa 0x1000000000000bf60a028759d187ee7 0x10000000000000b6108db6f704e01fb 0x708163ac067f025174f 0xbfb76a87fea2b1e6bd (M 0xfffffffffffa5bba110872bb0c5771 0x1000000000000fbf2dd520e3762dfdf 0x1000000000000a7b16128d72ed0d20e 0x10000000000001b80f45a6faac92e58 0xfffffffffff01044592b789aa5285a 0x10000000000125aeeb8ca48eafa86de 0xffffffffffff60a92c84fb82c95665 0x10000000000352c662cc6008d68607d 0xa9ef3cbd4eeaa8f7ca (Q 0x5ba15de430951c368f6 0x184ee0a8cc1312939e37 0x352d55282f9ecedb9099)) (M 0xfffffffffffc425741aab267d73434 0xffffffffffff6714047d849c028a8d 0x10000000000007d217367f1034ce9a1 0x10000000000002c561f442f530dd4d9 0xfffffffffff20539c900a284591a50 0x1000000000007d716a368c5706c421a 0xfffffffffff349c785e22cb458f74f 0x100000000001fd6b92e1815f181aef5 0x84c120cdeb5fe0f7f6 (Q 0x3c9cafcabee6e563c92 0x10072ca5d8df48991346 0x224858d01f5ce2ae373b)) (M 0xfffffffffffdc9cf3037aedc108f18 0xfffffffffffed5105fda727b122239 0x10000000000005b8b0654e6ea7ee7ea 0x10000000000002f199e7faeb148dfcd 0xfffffffffff59888579e04da4cbc0c 0x1000000000001ec1df1253dbdfeb0d6 0xfffffffffff133aef4ef579cd3ed71 0x10000000000108ce1119424f153c5b8 0x66f358ce0cc43ef72a (Q 0x280434006caf22d1ae6 0xa948cd6c5eda7b65c64 0x1633877492af29aeba8c)) (M 0xfffffffffffedda76ce907e4ca3645 0xfffffffffffecb5187285ecdbdeabe 0x100000000000043683159b127b97e34 0x10000000000002a23ed265f25992bac 0xfffffffffff91216e7fffed2e6afda 0xffffffffffff15478ad142e5bf3459 0xfffffffffff363add50f678242eec2 0x100000000000702e722c4d9d2203b02 0x4f7f28096b32c7493d (Q 0x1a7c6b401ae12d21eb9 0x6fd5f8566903e7638b3 0xe6dbe6221fe6d561cb0))

private def cneg_bt_162 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff1333d4020d95fc966805b) (L 0x100000000720489f92d9e8d4c645e49))) (N (L 0xfffffffda11e6aed969032cedc974f) (N (L 0x100000009c5fa1c5754bd0437704021) (L 0xffffffdecdd6b5a535e6c90a27ae40)))) (N (N (L 0x1000000608ae124a80a16e93fe5a31c) (N (L 0xffffff0934047b254e239d0e1cf511) (L 0x1000002352dfef13513a8abeee36fe0))) (N (L 0xfffffb67ce669d1d1d65545478bb10) (N (L 0x1000008c96910b9dbcb1358601781c0) (L 0xfffff06b3628c55e80ddbaf8f17f49))))) (N (N (N (L 0x1000019ce8338266949babe659dd18e) (N (L 0xffffd7d5593a3caba71bede1c5297e) (L 0x100003b0d29a6a1ad48d7530abc2455))) (N (L 0xffffada2f6913e442f4554b2a2ed9f) (N (L 0x100006d66dc6aae52fa993738d9d3c1) (L 0xffff75272473ad35513e7d0b0c3ecd)))) (N (N (L 0x10000a8dce643fb715e880ff88e2ed9) (N (L 0xffff3ab2460c08e6363bca00f1f477) (L 0x10000ddfdd0a27b9eb58c8507f38702))) (N (L 0xffff0efde6990d4f7cfd0025d9e19e) (N (L 0x10000fcf21fe68671df62e3803debf8) (L 0xfffefeedd3675a3611009654f5ced0)))))) (N (N (N (N (L 0x10000fd615124a9527324356de503ce) (N (L 0xffff0d7477b144eceddd8157bc786e) (L 0x10000e1c56c69c267938db0e5c66cad))) (N (L 0xffff336599a36148cbbf266350deb7) (N (L 0x10000b4b72e98c400974d152593c6ec) (L 0xffff6446b41a6df6e5c43efe12f28f)))) (N (N (L 0x100008309a1627a3691555be2bee6c1) (N (L 0xffff943b0977294b3e438a8b03a97f) (L 0x1000056b278c37e6aefddf0cd15adce))) (N (L 0xffffbbb9f4c9fc3095590fcaf55ee3) (N (L 0x1000034ab049e346f13cb4d42dc2377) (L 0xffffd82c50816d28edcf3160a50737))))) (N (N (N (L 0x100001d8a454b5f2a400deb3135ec5d) (N (L 0xffffea7f1769c2bec4f0c4cf111e9b) (L 0x100000f5f0f144e203dca956a951b59))) (N (L 0xfffff53458f9a854d6333f7af4e7e2) (N (L 0x100000773edd6e9bec3375c813b8fc1) (L 0xfffffaf0a2c82982405bbfb8acf0e2)))) (N (N (L 0x1000003614c81ffc01ad61aa323326c) (N (L 0xfffffdc70e7b31c6e66ec7c7b1f2a0) (L 0x1000001705ce38ed15fa0709e22f2a4))) (N (L 0xffffff150fe72e38418f14137fbe4d) (N (L 0x100000093a8aecf9cdecc845acf6a36) (L 0xffffffa483f9902b21714baf59a574))))))) (N (N (N (N (N (L 0x100000037e4ba45dcf5774b3d9be75a) (N (L 0xffffffde509676012f6e3035a3d62c) (L 0x100000014081315eaed027b35f4210f))) (N (L 0xfffffff43e16f3fee4dd81c142e2f6) (N (L 0x100000006d035932e5a60308d2033fe) (L 0xfffffffc19d373aa4e8ac828562d40)))) (N (N (L 0x1000000023445b776aeabe42df65d7b) (N (L 0xfffffffec4d2cdcaaf93144eea0bbe) (L 0x100000000adfb7fe7301f6e49434981))) (N (L 0xffffffffa10fb5c3af8be54596e02e) (N (L 0x10000000033390590ebe6d66a3bf5c8) (L 0xffffffffe4ab3b5ac08a8fb724969f))))) (N (N (N (L 0x1000000000e6cce0ae8aefe6876d99d) (N (L 0xfffffffff877bd71e48a34b7064c87) (L 0x10000000003e45784868f1772fb04c0))) (N (L 0xfffffffffe0279b71857b7642dbcc3) (N (L 0x1000000000101efd91495aac86d2823) (L 0xffffffffff7eb886bfa634e6a86d78)))) (N (N (L 0x100000000004029acdccb12153a4629) (N (L 0xffffffffffe07604d3123c44c26b18) (L 0x100000000000f5b3f18c2bd0651d08b))) (N (L 0xfffffffffff897a8294a213c627eaf) (N (L 0x10000000000038a62082b03b38a0755) (L 0xfffffffffffe52af2c944583a5fc51)))))) (N (N (N (N (L 0x1000000000000c98b9143350f36ca2f) (N (L 0xffffffffffffa235ba266d07c7cde8) (L 0x10000000000002b4524322c93457123))) (N (L 0xffffffffffffec34e6928e43f86e5e) (N (L 0x100000000000008fa81e79b215f0f75) (L 0xfffffffffffffbf5f4865266dd7d78)))) (N (N (L 0x100000000000001cd69eaee58a96461) (N (L 0xffffffffffffff33c199c779bf7733) (L 0x10000000000000059b19970f1c8c4b7))) (N (L 0xffffffffffffffd8eafda6b793cff2) (N (L 0x10000000000000010e5f06096427c7c) (L 0xfffffffffffffff8bfc156b56d4b8b))))) (N (N (N (L 0x10000000000000003168aefde7c9a4a) (N (L 0xfffffffffffffffeb1cf77ebb84e77) (L 0x100000000000000008c3e084650ac3a))) (N (L 0xffffffffffffffffc5925448c2e6b1) (N (L 0x10000000000000000182b61867d52c5) (L 0xfffffffffffffffff6128640b69d0e)))) (N (N (L 0x10000000000000000040caa51608e18) (N (L 0xfffffffffffffffffe5c0be800af9c) (L 0x1000000000000000000a8f84e5c6a54))) (N (L 0xffffffffffffffffffbc7843548bcc) (N (L 0x10000000000000000001acf6e99bb76) (L 0xfffffffffffffffffff56cf999fb2e)))))))

private def cneg_lf_162 : FastDTree := dleaf cneg_bt_162 0xfffffffffff9612f8ce5f98cc4169c 0x10000000000023edc216649d2900610 0x1000000000000bc189dcc9a09fa3ba0 0x100000000000006d051d8dccfdaec4d 0x6fda6f34aa3ba67bac7 0xbc38757187899b72bb (M 0xfffffffffffa5f68694e3453a5a0fc 0x1000000000000e378f032d759694f03 0x1000000000000a493acc9039b4b211d 0x10000000000001680c7059b6188fba1 0xffffffffffeff19ed476894853e51c 0x100000000001224bac20584b9f157ba 0xfffffffffffefa0fb51679162ce3cb 0x100000000003511064f261f920774a8 0xa61bf9dc50ba5798a3 (Q 0x5b2711e388f289b3c5c 0x183a516e2b75f7de2130 0x35138cf96e1349c29105)) (M 0xfffffffffffc4873ce8f5cd0471520 0xffffffffffff54d741deb22f43b250 0x10000000000007a684c006006dccf7b 0x100000000000026af0ad6a114ebbb1d 0xfffffffffff1fb6aa0ad4b8ab1afb5 0x1000000000007aa23041abe2ea8c9ad 0xfffffffffff308b7d2c6ecac1b0aae 0x100000000001fab2cf3dad6bd9ffae1 0x80602e3ed011836629 (Q 0x3c6d1dedbbe8154acdd 0xff9fa761d4bd7316cb0 0x22385ccc8691a6a5c308)) (M 0xfffffffffffdd04c33b06c30965832 0xfffffffffffec7be1b1e8c12a18694 0x1000000000000593aeb14dc2bda613e 0x1000000000000290a80ee5e00bc544c 0xfffffffffff59b1133210b3c2177ed 0x1000000000001ca79024c17cee28a8a 0xfffffffffff1107f6b7fb9b82db47b 0x10000000000105fc7af4fa82ef7c001 0x6237a1afafa4a83d3c (Q 0x280ea73554675729e96 0xa8c245922914dced452 0x1629a428867cb63e970a)) (M 0xfffffffffffee365483c849c290b7e 0xfffffffffffec1861090d10ba3eb17 0x100000000000041788ddfdf4e500e0c 0x100000000000023dcb619e1b3781554 0xfffffffffff91aa2fb8348ea430f97 0xfffffffffffefe3c7446566b3ef76b 0xfffffffffff355490bf1a151c5e0d4 0x1000000000006dc0432c817b5432a0f 0x4aa696c287e34af4f1 (Q 0x1ab1daaf19fdb9c5427 0x6f8155fcf87ae5f3c65 0xe67a7c2d7d04f63133f))

private def cneg_bt_164 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff10d8a472273196a9bbd7e) (L 0x1000000007435417ff063cf273ab604))) (N (L 0xfffffffd902ad51c1cf4047bf93b9f) (N (L 0x10000000a209781dabf899b3196cd52) (L 0xffffffdd56c0312af5fd22b1b924c2)))) (N (N (L 0x10000006589ca989c8a8ec88719d2f7) (N (L 0xfffffefa9ef614bd6998681fcecf79) (L 0x10000025a9692f6a0ca6e63bdb36d9d))) (N (L 0xfffffb11d93dd117bd230fe7e4682e) (N (L 0x10000097ce17b985c59121aa5b55ef1) (L 0xffffef12e63660d5806ab58c73568e))))) (N (N (N (L 0x100001c32f01c7579ed1b745cee409f) (N (L 0xffffd3dbfce7065ca973349a6cb640) (L 0x10000414135f934df9e10f623be4f93))) (N (L 0xffffa47daf91d979f9585d1da35174) (N (L 0x100007a3169074b59f848dd83bfb06a) (L 0xffff641de9dc32abbf55e3c4ddaee2)))) (N (N (L 0x10000be8a84641ff37af46c508f9656) (N (L 0xffff20438c612e0f8167c0b951036c) (L 0x10000fcf4334f553c01149be9686c24))) (N (L 0xfffeec119e03aba4c4649d06347a49) (N (L 0x1000122f3e1b3750e96a8d47cb8f3f8) (L 0xfffed6f1bbccaf477ba50c2cc557b4)))))) (N (N (N (N (L 0x10001261cc8069b221516d0a1213b7a) (N (L 0xfffee536f7e3644cae09ce25c16017) (L 0x100010860d436a6d194c8a9c042cb97))) (N (L 0xffff0f611c73f067a1b927a521c23c) (N (L 0x10000d56d992e4517d4d6179e45e3eb) (L 0xffff4751ed39a2d12e874105c83d9a)))) (N (N (L 0x100009c0af689c08d4db4dfe6983248) (N (L 0xffff7f25169ac94b2482459d5e1b9d) (L 0x1000068132d00dfbbe5bcb2f5d48e89))) (N (L 0xffffadb7bce0713884f1117fd7ec79) (N (L 0x100003fb8e4e6cdc9f7a91f6ea73218) (L 0xffffcfa0e302aebc0fb80b7d8ab614))))) (N (N (N (L 0x100002403a9290b7fdbafa4d583f747) (N (L 0xffffe5af5ed8495ce0774f4bd05b19) (L 0x1000012e16c564c36ce0a1272d9d534))) (N (L 0xfffff2b0f074ec06078839a231d60d) (N (L 0x100000938a9b3b138458b2fa077822d) (L 0xfffff9b77f2d9f0fb719bd3260dee9)))) (N (N (L 0x1000004364bd0e6959c16eea4f024b0) (N (L 0xfffffd3883573ca229b249b93fe076) (L 0x1000001ce41f7d1f1b883d38126695d))) (N (L 0xfffffed828f7f156fcc0c48ea1cbe8) (N (L 0x1000000ba9234b079aeac4fae709b3e) (L 0xffffff8c0409f7b37727b3a24809b1))))))) (N (N (N (N (N (L 0x100000047196f10c68a69d96cbb9ea2) (N (L 0xffffffd5022762635fe15d361e8d3a) (L 0x100000019a65ea40b3e85ffb0576ebc))) (N (L 0xfffffff0e55107593a266f326f5803) (N (L 0x100000008c7f18e21697549d6785f32) (L 0xfffffffaf56d1f012ebc8d28bf132e)))) (N (N (L 0x100000002dbe2ca0db5bd49223a5932) (N (L 0xfffffffe65e9edd204a4a99a1345bf) (L 0x100000000e314eb9d47a99ea2e66e65))) (N (L 0xffffffff83b3b06517e746d131624d) (N (L 0x1000000004344ffb47927d36d8c1fbf) (L 0xffffffffdbff45acea06c81fcf1f33))))) (N (N (N (L 0x100000000130f35018395ecdd7df807) (N (L 0xfffffffff604949c03fcd15bfa4962) (L 0x100000000052c56b22edf5f78859e22))) (N (L 0xfffffffffd58bbb1ec5f74c93ffced) (N (L 0x1000000000158e07ddd0f4a9b957e51) (L 0xffffffffff52a42d8c30118e306a79)))) (N (N (L 0x10000000000564a19088a13c76a1937) (N (L 0xffffffffffd5766ceb71714d8dd3cd) (L 0x1000000000014c554d6cb4997039112))) (N (L 0xfffffffffff5f3c14abe1d27decfff) (N (L 0x1000000000004d0e89f6ea1f8194a54) (L 0xfffffffffffdb662b47801e3bf3031)))))) (N (N (N (N (L 0x100000000000113afb7e8e9001b73ca) (N (L 0xffffffffffff7f5a52125f6f18b81c) (L 0x10000000000003b83bd6c01c5bfa79b))) (N (L 0xffffffffffffe4b38e12bd12812777) (N (L 0x10000000000000c6aaacde07e796be2) (L 0xfffffffffffffa66219cfd981346ec)))) (N (N (L 0x100000000000002818a7d8591c149e7) (N (L 0xfffffffffffffee3440c117165c2fd) (L 0x1000000000000007d5f6df5eaf78d77))) (N (L 0xffffffffffffffc93a40f0694f5b6b) (N (L 0x10000000000000017be9415fa09bcb5) (L 0xfffffffffffffff5c8e7a9aff31c49))))) (N (N (N (L 0x100000000000000045c9c64bdf049dc) (N (L 0xfffffffffffffffe26c0df4a8ab4b9) (L 0x10000000000000000c71b4950b96537))) (N (L 0xffffffffffffffffacd5f5a9a1d35e) (N (L 0x10000000000000000227d2919067a27) (L 0xfffffffffffffffff1cc42c56d8ebc)))) (N (N (L 0x1000000000000000005cebc66047523) (N (L 0xfffffffffffffffffda4381af8d222) (L 0x1000000000000000000f38976e28eb8))) (N (L 0xffffffffffffffffff9e6d8dc9b9d9) (N (L 0x100000000000000000026d51d39fab5) (L 0xfffffffffffffffffff0a5818907c0)))))))

private def cneg_lf_164 : FastDTree := dleaf cneg_bt_164 0xfffffffffff961dc55f007671e4e12 0x10000000000022374b077759c3b9b57 0x1000000000000b7f160796fd816a4c8 0x100000000000002634b20f35822fc9a 0x6f4657d8c8071972ee8 0xb7f59901a4aeb0b30d (M 0xfffffffffffa625cb2f3dd95274229 0x1000000000000cb84fc60bbbdb9f859 0x1000000000000a0979adc1e8a4f77e9 0x100000000000011a8200875859511af 0xffffffffffefd3e4579706785baecc 0x1000000000011eef3fd9c440071b725 0xfffffffffffe94dd336ae4d080285f 0x1000000000034f53372b6fdd62b977e 0xa18f9f765467a8878b (Q 0x5abf921edc4cf3b14c1 0x182604ecea71e3a7726f 0x34fa1081e3e1f478b684)) (M 0xfffffffffffc4dbe33fb71d37bf9be 0xffffffffffff431197c6b56604e149 0x100000000000076d1bd3a5e4a7aad61 0x10000000000002135ee9a448c4e2faf 0xfffffffffff1f234befcdd910aa876 0x10000000000077dac24feb21dbb3654 0xfffffffffff2c8cd420c72a8dee860 0x100000000001f7f9041f29d27a14789 0x7b5fe004e32a7098b4 (Q 0x3c4ef5d6d198f7e01c7 0xfecf5a9a50f5a970818 0x22288c21356e9d2d17b5)) (M 0xfffffffffffdd5e81ce18498064c90 0xfffffffffffebad370ac6c8f535fef 0x1000000000000560dbc22f2c49781d2 0x1000000000000232e53a6beda2dd2a6 0xfffffffffff59df2e8806d39a86a29 0x1000000000001a94cb7f2f1ed688b15 0xfffffffffff0ee2e5a29d5f70f3bc7 0x100000000001032d9e5d170c6323968 0x5cf7f8cb24d2b7b702 (Q 0x28276a4986d1e904630 0xa83dcb443cfb77f4ca4 0x161fd8b414714112d70f)) (M 0xfffffffffffee83a0df33dc657f00e 0xfffffffffffeb813fedaad3312f471 0x10000000000003eabe1fe7435b3e756 0x10000000000001dcc280d3fb507a194 0xfffffffffff92358a431806cd0ff9a 0xfffffffffffee79acfa5ba1390af4b 0xfffffffffff3478168585a03f2a1f3 0x1000000000006b56b04be1be972f93d 0x45655344e4663a8f3d (Q 0x1af0da9f426105fac31 0x6f2e46eacbecd52439d 0xe619d814fda024632be))

private def cneg_bt_166 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff0e7d74e240cd30bd0faa2) (L 0x100000000766b863fcbe695764af02a))) (N (L 0xfffffffd7ee4441dc2301fac98a5ab) (N (L 0x10000000a7dba0f775703669d99a437) (L 0xffffffdbd22238eafdeda49a0997c5)))) (N (N (L 0x10000006ac0ee6241b327caa27a3172) (N (L 0xfffffeeb497439d5855110447be853) (L 0x10000028232f57e25a2c7b4139cd41b))) (N (L 0xfffffab638a60de6f34af437f5d080) (N (L 0x100000a3d6c4779c0554d557e96462c) (L 0xffffed9f349df3a5f0dfff94b2a7e9))))) (N (N (N (L 0x100001ecc0f59f95dd864bd9257a215) (N (L 0xffffcf849c0b0b4432d117f2db009a) (L 0x100004811e7b41e4d9211a70ff1ec5e))) (N (L 0xffff9a632f597b64857276190b10a6) (N (L 0x100008866839bfc638eec35d29dfd82) (L 0xffff5118371c5ebad09114016b3607)))) (N (N (L 0x10000d6df29b032f9cd977f979a8b5d) (N (L 0xffff02727edfcf83c81bbc8413d77f) (L 0x10001200da152a02410751b3892627d))) (N (L 0xfffec449a9ef7a7724ba7ff08a87ca) (N (L 0x100014e73dd0908fd59719b535e3c3f) (L 0xfffea8f7858236e39a241ba2e70cb5)))))) (N (N (N (N (L 0x10001552a0d9371494d3a1b9edb4860) (N (L 0xfffeb6858c85ce583291355bb30dab) (L 0x10001355ff71f9edfc107f51a99bbf6))) (N (L 0xfffee537b6d7aca438af99b114185c) (N (L 0x10000fbe2b4256ed1554ff48deb4ed9) (L 0xffff252277dd5efbad606001b81894)))) (N (N (L 0x10000b9afd439de637beb81ae9ea605) (N (L 0xffff660b71c64f67fd6e754f371d21) (L 0x100007cd8518f614618a113d247f364))) (N (L 0xffff9ce84e5093ffecddca86f129bf) (N (L 0x100004d0a2003f489715655228d4d75) (L 0xffffc54b5cc1c7c1443ea89616d037))))) (N (N (N (L 0x100002bdfdc244404b99479df1e7f9f) (N (L 0xffffdfd247f63ca6a514f0493d3972) (L 0x10000172c5dce26d8af1526988b5248))) (N (L 0xffffef9af41f2fd53c5d7919ea8e87) (N (L 0x100000b6693aaf60cc37ed63ac9084a) (L 0xfffff834351485e8d515c442f299c7)))) (N (N (L 0x10000053ead439986a3a9383e12f83b) (N (L 0xfffffc86f41e3e471d42fa982ae52d) (L 0x100000243a11788691f723c2be9d5e5))) (N (L 0xfffffe8bc3f1726edfd351d2f4abbe) (N (L 0x1000000eb8cdbba2cfe90da021ecab5) (L 0xffffff6d128d6c24854dce8129c9fb))))))) (N (N (N (N (N (L 0x10000005a5e904b5df3e96cc4f04b2c) (N (L 0xffffffc92cd7b32fc2e79cf19c837c) (L 0x100000020d14247bdf71747a0d936cb))) (N (L 0xffffffec9cb406f3e397c1e8e766d4) (N (L 0x10000000b4ecab2534b468739fe5f93) (L 0xfffffff97cbdac13dc63c92917a247)))) (N (N (L 0x100000003b481acbf43e092d16bf331) (N (L 0xfffffffdeadd5d0e2fb8f75768e599) (L 0x10000000128241e3fec773fc9ebc227))) (N (L 0xffffffff5d6609264af8188ff973e6) (N (L 0x100000000584503926a2e479e59dd54) (L 0xffffffffd09d2105bd10956f9c6c43))))) (N (N (N (L 0x100000000192959916f103193d02f22) (N (L 0xfffffffff2c84bb1b18788f2609488) (L 0x10000000006ded2bbd63e51fe28767f))) (N (L 0xfffffffffc77362c45d6ae0a2c2160) (N (L 0x10000000001ccba7b09c0449f1cd09a) (L 0xffffffffff17bb12379714e30a6926)))) (N (N (L 0x1000000000073f27abc32afe0aa7268) (N (L 0xffffffffffc6ad924882dcff1ad163) (L 0x100000000001c11ef5f7758522395a8))) (N (L 0xfffffffffff261f4c56a9f74d78deb) (N (L 0x10000000000068b9d750444d3f13965) (L 0xfffffffffffce1e0733c78505df9ad)))))) (N (N (N (N (L 0x100000000000178c60ee7f62fe4cc2e) (N (L 0xffffffffffff4fb1e67534dd21d4b7) (L 0x100000000000051c943014c3c33cf99))) (N (L 0xffffffffffffda621c5a6e841ea3ee) (N (L 0x10000000000001128019a96d7db2d80) (L 0xfffffffffffff83d75c6d1217ba150)))) (N (N (L 0x1000000000000037b3349f37732b6c8) (N (L 0xfffffffffffffe7367ccbbd7fb7408) (L 0x100000000000000af16dfbbc61f7147))) (N (L 0xffffffffffffffb34e55af1cfe7152) (N (L 0x1000000000000002155b41d328eb73d) (L 0xfffffffffffffff19f1c250a1e205f))))) (N (N (N (L 0x1000000000000000627c334dd6f8c08) (N (L 0xfffffffffffffffd626ef836a4aa31) (L 0x100000000000000011a6ccb74949928))) (N (L 0xffffffffffffffff89bbf36082e801) (N (L 0x10000000000000000312b8ec13d7f2f) (L 0xffffffffffffffffebb38807d298ab)))) (N (N (L 0x100000000000000000852485fab147e) (N (L 0xfffffffffffffffffc9cb576d8ca1e) (L 0x10000000000000000015eb16a732345))) (N (L 0xffffffffffffffffff73263b5988a4) (N (L 0x10000000000000000003831cf2be7e4) (L 0xffffffffffffffffffe9ba444c5644)))))))

private def cneg_lf_166 : FastDTree := dleaf cneg_bt_166 0xfffffffffff961e716b20c9fa1b1b7 0x100000000000208b97cde3b9456ae2e 0x1000000000000b2f7fcf7be4d28ef40 0xfffffffffffffe3d6cce1edd0cccbd 0x6ec51b8cb35fa0f9043 0xb2fa74c4bd4a3d6059 (M 0xfffffffffffa649f5e8627eabb8e99 0x1000000000000b436da75029ec1a031 0x10000000000009bca3a6f9bb24904a4 0x10000000000000d1a2b3a60a4749468 0xffffffffffefb70cb0204a73e96864 0x1000000000011b99c16906063ae3f6a 0xfffffffffffe3109f1d9b1d7e89df9 0x1000000000034d8f2b44568d13280ea 0x9c574bb2d398d4d71f (Q 0x5a6a5be5662a31ef60f 0x1811fc5144cf1663a559 0x34e0de3732908cc16be7)) (M 0xfffffffffffc523fcb023ef3f3f3ec 0xffffffffffff31e2baab5026973ccb 0x1000000000000726ad2e15d6e40f087 0x10000000000001c0d69843f7095dc73 0xfffffffffff1e991c49b90f25f9d12 0x100000000000751b2b538b4e46a3862 0xfffffffffff28a00fd4900a946186e 0x100000000001f53e5f6a33283d77999 0x75cea29814464b286c (Q 0x3c40b257a40a7cea258 0xfe01f8575ea2be815b2 0x2218e62edb87c871ba9a)) (M 0xfffffffffffddaacf6d32771a13268 0xfffffffffffeae700832d608e1fef2 0x1000000000000521089b89d45d98e09 0x10000000000001da737023df84be4df 0xfffffffffff5a128ac4ba3cd8d255a 0x1000000000001889940afe8138b46d7 0xfffffffffff0ccb5fcea79209b084c 0x10000000000100618f400f783f3f17e 0x57424c059b5f026117 (Q 0x284c0f2d1a2e22d1773 0xa7bb6cb07fe6e61ab7c 0x161624ff1b00340faf8f)) (M 0xfffffffffffeec304cf089cf60200f 0xfffffffffffeaf1af73f5d9b05ad41 0x10000000000003b0f46f546b43d845c 0x10000000000001813f14effa29cf19e 0xfffffffffff92c3463e7bc052ef8b7 0xfffffffffffed162a1536b1b779e25 0xfffffffffff33a5242e4c6d91bf7a9 0x10000000000068f1bbfa9bb27e726a1 0x3fc7cf4ebadf412372 (Q 0x1b365cb521b5fcc40cf 0x6edccee8118c15c2c8e 0xe5b9fcb734325c49ad4))

private def cneg_bt_168 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff0c2245525a68cad0637c5) (L 0x10000000078a75838c026e039950ccd))) (N (L 0xfffffffd6d49e6a7adaa460c45942e) (N (L 0x10000000add6e0ce704283afd1f3b8d) (L 0xffffffda3f9ce3f744920b09deadaa)))) (N (N (L 0x100000070325194d7abd0cae5a6e0f3) (N (L 0xfffffedb2b114686e9df7ebddfded8) (L 0x1000002ac201bb26840f009603159a4))) (N (L 0xfffffa54977a601104f8225ddc9056) (N (L 0x100000b0be569a7f1c3a1f7b07767cf) (L 0xffffec0e248940ca586b6fd2933a2a))))) (N (N (N (L 0x10000219e0e43d05efd2503afe50798) (N (L 0xffffcac726373c8b3d4fcced765e32) (L 0x100004f8dad4cb826fd4c19b18680e5))) (N (L 0xffff8f3b5830ca925327e8e2e0629d) (N (L 0x10000982c08c514f178a82616096963) (L 0xffff3bdde9b26f68211433e9f4d383)))) (N (N (L 0x10000f229c79a42c0f03fa2b319df9b) (N (L 0xfffee0d568b36109ffb3b8460a2fce) (L 0x1000147d15273e0d5cc4ac69ec84bf4))) (N (L 0xfffe9700516ded80dcecd673d8935a) (N (L 0x1000180352c6766bba90ccb9ef19757) (L 0xfffe74220a24f175cac43811ecaa67)))))) (N (N (N (N (L 0x100018b7afb16c041a81b482ba91b63) (N (L 0xfffe80608f3d52227e365d9f538e84) (L 0x1000169c87c189c582d19939721b0d5))) (N (L 0xfffeb3e5b96a096a1faa8bf20959c4) (N (L 0x100012910c6a9fde690add2e9319b1e) (L 0xfffefccdcad2420b5f21e9cfbf0ea5)))) (N (N (L 0x10000dcce2eb57650ce5ccec9a90cf4) (N (L 0xffff482fe58b6ae302eeeb3ab78258) (L 0x1000095a6dc09ba3e7d375d968a8c2a))) (N (L 0xffff88bff847feca9d64626eacdfb0) (N (L 0x100005d12511909c657ef9c29951d87) (L 0xffffb8ce2a0e4cc3e1194a29ee96a8))))) (N (N (N (L 0x100003569028133c28bb4cbe37e7631) (N (L 0xffffd8ae488278b9f644000bc9a1a7) (L 0x100001c6ba8c1ccfe3a1ed4e2c16702))) (N (L 0xffffebd1bbdedee159c3ea2b6a82f4) (N (L 0x100000e1594e6a1aa9d84297690a83e) (L 0xfffff65593aeb31884312ae243d846)))) (N (N (L 0x100000686953c7dce713069691f1b84) (N (L 0xfffffba9f2c7bdf46681d18c612e17) (L 0x1000002d63b9d9093a14bba67d74e78))) (N (L 0xfffffe2c032fe9205bceb2285671f5) (N (L 0x10000012926e72fee32df2677c67c80) (L 0xffffff46059d5af8efaf734045b8b5))))))) (N (N (N (N (N (L 0x100000072c536264771aa3575cda310) (N (L 0xffffffba241986840535465d8c11b8) (L 0x100000029f4370adeb7b0d6bc6f5d4f))) (N (L 0xffffffe7223ea5f0b91ab4cb44813a) (N (L 0x10000000e8cbd4027ad6444cb816335) (L 0xfffffff797dea39af84b2884f5168e)))) (N (N (L 0x100000004cc3be505a334ceb07e6f8e) (N (L 0xfffffffd4b76db6dcf488800785ec3) (L 0x10000000181e232d6d46aa72ac0b06e))) (N (L 0xffffffff2b77d6515d80d9829b2954) (N (L 0x10000000073baa3803059307b68b472) (L 0xffffffffc1aeeb137b307d08e30a64))))) (N (N (N (L 0x100000000213083458feee49e0f5736) (N (L 0xffffffffee834dc817143b6162e12d) (L 0x100000000091de22b7cbeb6267c81fb))) (N (L 0xfffffffffb4bd57dbf23b3f2bf813a) (N (L 0x1000000000266f9a238f72927be4d97) (L 0xfffffffffec910db84e4e8c5934b83)))) (N (N (L 0x100000000009baa5ba6cce9158dd4bf) (N (L 0xffffffffffb2d22314c2d4c1a98da0) (L 0x1000000000025e6df52f15f223d3835))) (N (L 0xffffffffffed8f96add82276ee7a70) (N (L 0x1000000000008e352c2e996b9a0794c) (L 0xfffffffffffbc1313bbf916e64be1f)))))) (N (N (N (N (L 0x1000000000002027b243532d09a5300) (N (L 0xffffffffffff0e977eda6c58f406a0) (L 0x1000000000000704b5d04b47e768178))) (N (L 0xffffffffffffcc35d96935a2220974) (N (L 0x100000000000017af2fa0a6ef40e1a6) (L 0xfffffffffffff5422dd5a80b41b4d1)))) (N (N (L 0x100000000000004d4edbd9413585326) (N (L 0xfffffffffffffdd81607b2beea4e97) (L 0x100000000000000f44e2b5ade2ca2d1))) (N (L 0xffffffffffffff94b4a8ff1513adee) (N (L 0x1000000000000002ec1d64b0bc37081) (L 0xffffffffffffffebc78b07a751d530))))) (N (N (N (L 0x10000000000000008adbd88b28da4d7) (N (L 0xfffffffffffffffc4d84535a24e170) (L 0x10000000000000001904054f8e38cfd))) (N (L 0xffffffffffffffff57f7ab2f9b8bab) (N (L 0x100000000000000004609c05e5fda81) (L 0xffffffffffffffffe3037c9ed68a1b)))) (N (N (L 0x100000000000000000be9a668549f42) (N (L 0xfffffffffffffffffb2350d5c50f67) (L 0x1000000000000000001f88ac55392f4))) (N (L 0xffffffffffffffffff34dba7c7c2ac) (N (L 0x1000000000000000000513ee4fa573a) (L 0xffffffffffffffffffdfb855a3bfb2)))))))

private def cneg_lf_168 : FastDTree := dleaf cneg_bt_168 0xfffffffffff9615cbc087ea3dbe160 0x1000000000001eec835f8cc77a74855 0x1000000000000ad3e5afb6d0026a176 0xfffffffffffffa7f6c16e1d877d428 0x6e563dc8671d359fb4c 0xad54f9d813fae652e7 (M 0xfffffffffffa663dd8d745ce3111ba 0x10000000000009dac1ac388f841c4e5 0x1000000000000963d689e6bd03e7234 0x100000000000008f754a9dfd8c614b7 0xffffffffffef9b105737c17ac9d4c0 0x100000000001184b4a833952c0dd0a0 0xfffffffffffdce8e83250c9cda30f6 0x1000000000034bc48faed0f59e7a307 0x96821a8124ccfdc2b8 (Q 0x5a267349316afbf4f5b 0x17fe3880bcdd2a966c42 0x34c7f4a01725f115b962)) (M 0xfffffffffffc5606d4a3aa0d3f97c3 0xffffffffffff216817f65c80b969d2 0x10000000000006d455cbecb9a131215 0x100000000000017556065646778d54d 0xfffffffffff1e17bec78f08c67ad60 0x100000000000726375f3f2a0fd619ee 0xfffffffffff24c4c6fd23b66ba3bfd 0x100000000001f2830cd091cacb12538 0x6fbc52425c7322cf78 (Q 0x3c406607bb1c860faf4 0xfd378e7bf7d89602069 0x22096a5a3951958f74e1)) (M 0xfffffffffffddea9a22e64ded8dc27 0xfffffffffffea2b1427204bc39aed1 0x10000000000004d551db1d56be741d9 0x10000000000001894962b4bea1f8fa9 0xfffffffffff5a4ae3ddee236da194f 0x1000000000001685ecd5959133d9e89 0xfffffffffff0ac10c993c604eeea7e 0x100000000000fd98603d0521a8581dd 0x51256eb05ab5fd21da (Q 0x2879e7745a5c100fa6a 0xa73b308fef0ba28ba1d 0x160c88ed161927ae02a2)) (M 0xfffffffffffeef57593b57e4feb39d 0xfffffffffffea6b8577cfeeb9d33b2 0x100000000000036b4852273bdeb3bca 0x100000000000012d30f5bf9dd781616 0xfffffffffff9353339e335275f850a 0xfffffffffffebb93f3d03b8369462c 0xfffffffffff32db725c75dc9f68e0c 0x10000000000066916800cb5a5f48e3c 0x39dac8cb75b9f6dfcd (Q 0x1b7f5042451366abd83 0x6e8cea264dea956f083 0xe55aec5abb04a625fbe))

private def cneg_sub_18 : FastDTree := (dsplit (dsplit (dsplit cneg_lf_154 cneg_lf_156) (dsplit cneg_lf_158 cneg_lf_160)) (dsplit (dsplit cneg_lf_162 cneg_lf_164) (dsplit cneg_lf_166 cneg_lf_168)))

private def cneg_bt_171 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff09c715c2740464e3b74e8) (L 0x1000000007ae8b76acd24af71190be3))) (N (L 0xfffffffd5b5aeb6f06c839468ac679) (N (L 0x10000000b3fbfe0b5d2df50c909631d) (L 0xffffffd89ece78291b921bc69b18ea)))) (N (N (L 0x100000075e007858936dd6629e1aa60) (N (L 0xfffffeca3b1265bc37d4a601a3134e) (L 0x1000002d87c3e239d1c14f574d25ff3))) (N (L 0xfffff9ec9c3a7a243400850fafd90c) (N (L 0x100000be935b2d4d119e85273e1249b) (L 0xffffea5d97cd7b83538eeffe1f3a75))))) (N (N (N (L 0x1000024ad678a1bca78cfdb0c3d65d1) (N (L 0xffffc59ae7e11bbee9a89c0c7ed3ff) (L 0x1000057c4311a6456704c48e2af9095))) (N (L 0xffff82ebd55bd40b7c2bd5b2342614) (N (L 0x10000a9ab8b746fc44e579432329ae0) (L 0xffff243106cebe61b4b473ca63e084)))) (N (N (L 0x1000110c20044c635f57e8392260ed2) (N (L 0xfffebaf653d6f0cea90ddfe7232c87) (L 0x1000174d6f27d6dfb7b34581e1daef6))) (N (L 0xfffe637ac180ed66d17d2af525ce2d) (N (L 0x10001b914d80b2170677ec5ef87fe2a) (L 0xfffe3775891b751b25f90d858bf045)))))) (N (N (N (N (L 0x10001ca242fdd790dc2c1eea2100187) (N (L 0xfffe41a23ae327d08261477723966f) (L 0x10001a6c86e52bb87c40803f55eb903))) (N (L 0xfffe7a3e04fd35847770b59135bcc9) (N (L 0x100015e1b502f828b7ff15b5feaf3ea) (L 0xfffecd418bd2d00300e6322a4f604d)))) (N (N (L 0x1000106615f81cf532d330a194eee6e) (N (L 0xffff24b20c207246d6c740b73ed452) (L 0x10000b34237e4950f0489992699e1c4))) (N (L 0xffff709890c72660afca167b948254) (N (L 0x10000705b8a6d7087dd7a2c2f426035) (L 0xffffa9b915c0dd22502f78014a6f3f))))) (N (N (N (L 0x1000040f85d13205b83863127e5cb2b) (N (L 0xffffcffdd6ed7399e8b6ab803d666b) (L 0x1000022d466d4aabab0d26dbffe2ab4))) (N (L 0xffffe72d832e06e3d8b53f4a0c6f23) (N (L 0x100001162e76ad3aac41efc4490d030) (L 0xfffff40683d9c47d576961eab2312a)))) (N (N (L 0x10000081cf73d4c9ad0a462e981cfec) (N (L 0xfffffa9714665adaea475c21d4cc2d) (L 0x10000038d34dcadb613a1406be82c62))) (N (L 0xfffffdb416f27fa4df70306a75fd87) (N (L 0x1000001769186f716675cd9f63e64d2) (L 0xffffff14c76af19f6c036760905d35))))))) (N (N (N (N (N (L 0x100000091a4d795e4a258a7aaacac59) (N (L 0xffffffa70e2afe601136115725bb08) (L 0x1000000359752a2d97983a437607be8))) (N (L 0xffffffe0221588920d2a0cf327039d) (N (L 0x100000012b4c11320882f5bd997085a) (L 0xfffffff5283f5f8b25dbac728d2b88)))) (N (N (L 0x10000000635288a576fc0009466ba18) (N (L 0xfffffffc7d24798ecc6c7652225acf) (L 0x100000001f668746c9bf77bad854598))) (N (L 0xfffffffeea6f4867ec296b88be76dc) (N (L 0x100000000979ae798f0503e26bc4a30) (L 0xffffffffae1dd734d2f88ce9fd53e5))))) (N (N (N (L 0x1000000002bbe0b2a4b287ebc40b236) (N (L 0xffffffffe8e236bf94aa7b0097fa08) (L 0x1000000000c165d3f9cf4b0310b6d69))) (N (L 0xfffffffff9bebf4c6a97e23f2d54d8) (N (L 0x10000000003342b27e9d020eed355bc) (L 0xfffffffffe601c80ac499ca2f163ed)))) (N (N (L 0x10000000000d0cfd78a9b113890dbb5) (N (L 0xffffffffff982c63fea8eb955b3a43) (L 0x10000000000332232751f0e842e50a0))) (N (L 0xffffffffffe70d9ef46e73ae0e54f6) (N (L 0x100000000000c0f03ff08ad68b1d949) (L 0xfffffffffffa395d20a89a78718c22)))))) (N (N (N (N (L 0x1000000000002bde9aa5e3db6b3927f) (N (L 0xfffffffffffeb5bc027992938d7f87) (L 0x10000000000009a0c954d3b332e89cc))) (N (L 0xffffffffffffb8c26f67e3312a1db8) (N (L 0x100000000000020aaf6a607cccc1e90) (L 0xfffffffffffff124f331352e105b21)))) (N (N (L 0x100000000000006b34644a8513671b7) (N (L 0xfffffffffffffd009cbe8d7a0cf216) (L 0x100000000000001549580ad40b52c9b))) (N (L 0xffffffffffffff6a07442fe231340b) (N (L 0x1000000000000004186b91254649a1e) (L 0xffffffffffffffe396c2231282eb11))))) (N (N (N (L 0x1000000000000000c39c203452cdaa4) (N (L 0xfffffffffffffffac74330a469605e) (L 0x1000000000000000236babecb351c6b))) (N (L 0xffffffffffffffff1178b513f5845b) (N (L 0x1000000000000000063ac60f0759678) (L 0xffffffffffffffffd6a50ce82aaa32)))) (N (N (L 0x100000000000000001109e054b21b1b) (N (L 0xfffffffffffffffff9074ec24999a1) (L 0x1000000000000000002d53b5a8ef69d))) (N (L 0xfffffffffffffffffedb4843635f42) (N (L 0x1000000000000000000755bbfb220f7) (L 0xffffffffffffffffffd1421645d8b5)))))))

private def cneg_lf_171 : FastDTree := dleaf cneg_bt_171 0xfffffffffff9604ec56dc370d0e127 0x1000000000001d5bb94cfa37a247e65 0x1000000000000a6dab6e88ece771b11 0xfffffffffffff7469406acb847a685 0x6df8cdb8720cb2fcc66 0xa71553a56844199e9b (M 0xfffffffffffa674a16d5ab7b099753 0x100000000000087ff593282db75394e 0x10000000000009007528d0164c0822e 0x1000000000000055ca1f2aec7d262b7 0xffffffffffef7fe869c27c767acd52 0x1000000000011503f32c6d659a46c18 0xfffffffffffd6d63beeea5f435b274 0x10000000000349f3afa372afdba0deb 0x90211f68764875ca2a (Q 0x59f26dea55e48a3c523 0x17eaba103309aea6e582 0x34af525285a9a795914e)) (M 0xfffffffffffc5926068f9f1a409dc3 0xffffffffffff11bc2b50fb62fc8b27 0x10000000000006777710ad108a62eba 0x1000000000000132a588234f03f6068 0xfffffffffff1d9ee04cbbd28d68d83 0x1000000000006fb3abd0d28226ccd6f 0xfffffffffff20fa9439722f79cdd02 0x100000000001efc735e6aa5cf1a623a 0x693a4f1433e0879fcd (Q 0x3c4bcf8dbdd2c86de9a 0xfc70243e9ec83dbdb8b 0x21fa180b031f06e51e57)) (M 0xfffffffffffde1f162d412fef722dc 0xfffffffffffe97b19004f16775dcbf 0x100000000000047f17e79a68f7173d7 0x1000000000000141282ff808abf5b32 0xfffffffffff5a87fe12357ed244018 0x1000000000001489d84f8f8f2828608 0xfffffffffff08c396d1063a14ae39a 0x100000000000fad222aeca21071693c 0x4ab13262606ec64a61 (Q 0x28ae1fb7a3c5e5ff9da 0xa6bd164baae370c4900 0x1603045c9afbf5f55101)) (M 0xfffffffffffef1c2da52a4b1fb6985 0xfffffffffffe9f068e23531d43b566 0x100000000000031b1976fe1811ea898 0x10000000000000e252c11f5bb83d988 0xfffffffffff93e529d23c0973398ab 0xfffffffffffea62ecb90cceea20d5e 0xfffffffffff321abca6a3715faeacd 0x1000000000006435b581dd7d0950b67 0x33ab3e2503bf0c02e8 (Q 0x1bc8bc91788c152ea52 0x6e3e8dc5adcd4f98570 0xe4fca8ad8a58f44c80a))

private def cneg_bt_173 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff076be6328d9ffef70b20b) (L 0x1000000007d2fa3d5f2e0031cd6ed6d))) (N (L 0xfffffffd49168128f4efbb06f2fba2) (N (L 0x10000000ba4bc1041f1f9447175472c) (L 0xffffffd6ef536597444171b911e004)))) (N (N (L 0x10000007bcc321043ac6c072a04a283) (N (L 0xfffffeb8706d72a3399a3c57c86056) (L 0x10000030766e44d6e9783780074626c))) (N (L 0xfffff97de8da3cb884cbc1408a6ac5) (N (L 0x100000cd65376e63fea22353a31b2e4) (L 0xffffe88b4cfa4fc75b1d0892dd9e10))))) (N (N (N (L 0x1000027fee846cfe882080a446c95c4) (N (L 0xffffbff67e9fe86dde5c7b2a92eead) (L 0x1000060c67236e5ef1906fb4ba7813b))) (N (L 0xffff7557eac6121513c0ee9c622ec0) (N (L 0x10000bd12abf4f5ee1f6c547d550640) (L 0xffff09cd290f3015cacff8009a7376)))) (N (N (L 0x1000133090d78c97c1f92dfa54ca597) (N (L 0xfffe9051b0ba7cdfcee7e207a9b500) (L 0x10001a7c88829c41e120afd02f22d3b))) (N (L 0xfffe28e67d9ab233d724a69e192b02) (N (L 0x10001fa0d20d4c8a519775cea475f23) (L 0xfffdf1d399380006a0eb93aae0ac03)))))) (N (N (N (N (L 0x100021261ddd3a4c23e339c0ce6269d) (N (L 0xfffdf8f93400a7b6bb5ee60b3f34b7) (L 0x10001edbc3f2a2ed1617cef5f037020))) (N (L 0xfffe36e3a92a4ab90116db45acc96f) (N (L 0x100019c55980fc1159a2cd1c3fc6a93) (L 0xfffe953d04db3a1302a827559495d0)))) (N (N (L 0x1000137907aba9584a830c23bc6b0ce) (N (L 0xfffefa89593e2c6c6b3b4782bbe2e9) (L 0x10000d691bcc3c61ea15da6e39632ee))) (N (L 0xffff53ac9419182e9bebf2e23363b4) (N (L 0x10000878a94d9b60abdcf6206fd2a48) (L 0xffff9785ac7e19bee3851fb4e14d9d))))) (N (N (N (L 0x100004ef949b90dee6b8cf9350d3fe7) (N (L 0xffffc56cf9bdf9779e2c116a265b81) (L 0x100002aa6f6eb6276b26f31a5d3d700))) (N (L 0xffffe17de5edc346b115b544dd0533) (N (L 0x1000015723dc688722b9a2270a7bb0d) (L 0xfffff12d2aa597b8c870320e99b0f5)))) (N (N (L 0x100000a1438b12d13aa601395ebaa2c) (N (L 0xfffff9417bab694ea3c946c9ea5e47) (L 0x100000471656baed09490f509f7e3dc))) (N (L 0xfffffd1e034f3a49ad049b9ea14cc8) (N (L 0x1000001d7c89eb5903400eb030f3cee) (L 0xfffffed6bb6e0d981e1fc73116c202))))))) (N (N (N (N (N (L 0x1000000b8ad156bdd9f3a7e7b55a773) (N (L 0xffffff8ed8765bf843719d3759853d) (L 0x10000004466c272d2c42787da791073))) (N (L 0xffffffd731c4fd397d679ddd651f14) (N (L 0x10000001807c09464cd51270b9df53b) (L 0xfffffff206d14f7d0665e5781b3837)))) (N (N (L 0x1000000080678997bd7f40c9e4f7364) (N (L 0xfffffffb724e113b13973cfb141395) (L 0x1000000028d954f6dd04580e5170bfd))) (N (L 0xfffffffe95ccad1113364a60dd4007) (N (L 0x100000000c670580e07ea28983204a1) (L 0xffffffff947ec75930381455e4170f))))) (N (N (N (L 0x100000000399a490de74223ebd3addf) (N (L 0xffffffffe177be854a6567e2af7b6d) (L 0x1000000001003364a6a59295f4e85c9))) (N (L 0xfffffffff7b080c9bc630c8b00d09c) (N (L 0x1000000000444e82499df3e5a28f761) (L 0xfffffffffdd4330650bc3e091c28f4)))) (N (N (L 0x1000000000117ddbe4d07d9ad676c7f) (N (L 0xffffffffff7471aab282ffbaf0d7eb) (L 0x1000000000044ed062024b2b8a77e04))) (N (L 0xffffffffffde470f543c9aadd9e541) (N (L 0x100000000001058af4b5e607dc9493a) (L 0xfffffffffff825fe9f6145ff5e5726)))))) (N (N (N (N (L 0x1000000000003bccdf2878a2d2607a9) (N (L 0xfffffffffffe3c8f620436cf9268c3) (L 0x1000000000000d325a534b5ba6a369d))) (N (L 0xffffffffffff9e169ebacf4b75cd37) (N (L 0x10000000000002d0508691c88aceca4) (L 0xffffffffffffeb78e4ec3647fbd5b6)))) (N (N (L 0x1000000000000094888074e573aacc1) (N (L 0xfffffffffffffbd5f2a86dc0a9bc86) (L 0x100000000000001da63a26bd77fdd66))) (N (L 0xffffffffffffff2e8f5096b37d7673) (N (L 0x1000000000000005bbfaebdb0cf6e7d) (L 0xffffffffffffffd81da81806a4a988))))) (N (N (N (L 0x1000000000000001134fbdf1dac676e) (N (L 0xfffffffffffffff8a1c4ede310ed26) (L 0x1000000000000000321bd6b091004f5))) (N (L 0xfffffffffffffffeadb364beec95a7) (N (L 0x100000000000000008db8d02e571b94) (L 0xffffffffffffffffc50cec334d2b96)))) (N (N (L 0x10000000000000000185929bbe2ef16) (N (L 0xfffffffffffffffff6034e7e52eabf) (L 0x100000000000000000411849d26dc09))) (N (L 0xfffffffffffffffffe5a9637f19ba0) (N (L 0x1000000000000000000a95ec929b309) (L 0xffffffffffffffffffbc60ca3a1c42)))))))

private def cneg_lf_173 : FastDTree := dleaf cneg_bt_173 0xfffffffffff95ed2b941032bd8f5d4 0x1000000000001bdaac383180b661111 0x10000000000009fe70d1d894e506093 0xfffffffffffff4ac341ff503201f5f 0x6dab700d37b3271cc79 0xa04de6263162c46de7 (M 0xfffffffffffa67da0a6a125003fa54 0x10000000000007347a551822c27655d 0x10000000000008941e1080f4c2a8469 0x100000000000002632172808fa437bd 0xffffffffffef658e9f28e787b3a0e5 0x10000000000111c3d10c155e3d396d2 0xfffffffffffd0d82be58ce67322deb 0x100000000003481cd340fd31678fc6f 0x8947728b6ffbd4efae (Q 0x59cc812470975e80f51 0x17d7813c855ba3db17ec 0x3496f5f1e1ff8f8ec6da)) (M 0xfffffffffffc5bb4011e99630c3c57 0xffffffffffff02f5e8187d27b446c4 0x1000000000000611ad8ba05bab363c9 0x10000000000000fa4e7f3333a594916 0xfffffffffff1d2e366a200a01dfec6 0x1000000000006d0bd4d0570ec421377 0xfffffffffff1d4115e1d70ee2b6889 0x100000000001ed0b0236a96e1813664 0x625bac6b57db8e07c9 (Q 0x3c606fb90c04f077ba7 0xfbabba173e83c41a794 0x21eaeeaadc3b018189ea)) (M 0xfffffffffffde49b56d7cada192c53 0xfffffffffffe8d87dc3dcdf8efe657 0x100000000000041ff5c0cb6f935bc8f 0x1000000000000103927a260dedb7c5a 0xfffffffffff5ac9a56d3d763712063 0x100000000000129557975e92d061c65 0xfffffffffff06d2ac8c1b903aec413 0x100000000000f80ee6b58f246bedf2b 0x43f6a1c895065485a9 (Q 0x28e5d96619b5f5147a5 0xa641164e95a05010158 0x15f99726eb7c13e82c35)) (M 0xfffffffffffef38a4315dbf7f353f2 0xfffffffffffe981c86dcc17310d060 0x10000000000002c20190ea9096268a8 0x10000000000000a22107a19e2435d07 0xfffffffffff94790754ce09fa10004 0xfffffffffffe91331b9012857141b4 0xfffffffffff3162c172eda38989f85 0x10000000000061dea4ff058f9a86520 0x2d466cb2ac7db9d064 (Q 0x1c0fd5bb6c44ca8fc47 0x6df1a881ba43c5483a1 0xe49f32c5d9e50d994d6))

private def cneg_bt_175 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff0510b6a2a73b990a5ef2f) (L 0x1000000007f7c1d7a3158db3cceb163))) (N (L 0xfffffffd367bd68a9f868cf908f2f3) (N (L 0x10000000c0c6f3fbbb330165dbb6e99) (L 0xffffffd530c6420c047d489259b7be)))) (N (N (L 0x100000081f901dd3a111780a8af2fa4) (N (L 0xfffffea5c1c6cfeec38b9b2339815f) (L 0x10000033900f06d88ae8082b36087e9))) (N (L 0xfffff9081a8f861d8205a6500b7914) (N (L 0x100000dd4433c05ac8c59a68bea4eb8) (L 0xffffe694dd4facc6cf17d451caaeb8))))) (N (N (N (L 0x100002b97b5558b9bc16a23b01e6858) (N (L 0xffffb9cfcca5f14a7de5956a6ce6b6) (L 0x100006aa6df2865198b6d966a51a237))) (N (L 0xffff666040e349a62ede45c6e1f678) (N (L 0x10000d2937652c08cb5b9eb8f3092a7) (L 0xfffeec66e0e0b1b345ed14262db7e2)))) (N (N (L 0x10001596abe1e84806e41e5014646d4) (N (L 0xfffe6054da431e92bd611a11bdaaeb) (L 0x10001e164915c2daa28eea9759b7f8c))) (N (L 0xfffde656848cd07cc3834442e5ff5d) (N (L 0x100024439312ffa0e4f9888231db5d7) (L 0xfffda1f696da2034738bd22974f751)))))) (N (N (N (N (L 0x10002659d388b3412a116529821a847) (N (L 0xfffda4e250a4ba6ddbb25c7d314545) (L 0x100024035a410f0d6063210f5de21c5))) (N (L 0xfffde842908d5bba13f502838c7ed6) (N (L 0x10001e54a3f263a730e9dc9bc0c44d7) (L 0xfffe53498f961fc3e5a7e8f7d60228)))) (N (N (L 0x1000171b5ae201a803793fc27dc4223) (N (L 0xfffec87e22251e058a7f2aad42bb5a) (L 0x1000100a7180ec6b229627fec88f933))) (N (L 0xffff311164ed7516f340ac21a7059a) (N (L 0x10000a363f71325d42efe7d331a3ff0) (L 0xffff8192f1867465b0e0a1caa3d559))))) (N (N (N (L 0x100005fecd884144be6affeb056d795) (N (L 0xffffb8965b291405892f5c3658f6b6) (L 0x10000343152e377db501c01c93cf4ce))) (N (L 0xffffda880cda0bfab21a4559a2ca56) (N (L 0x100001a6f2984c0d298c72c6e9f18d5) (L 0xffffeda9dbd5d19a800f026364f124)))) (N (N (L 0x100000c82f7c055c22ffb52e8689ebc) (N (L 0xfffff79948e075f699b518e07af79b) (L 0x10000058dc1a24ae261fb3a2ec0c709))) (N (L 0xfffffc6258852c1d320ebc7ec0f2e8) (N (L 0x100000251c41158b1e7e93e2e92ae54) (L 0xfffffe889d0b7e281befb78d9099f7))))))) (N (N (N (N (N (L 0x1000000e9fbef2a5a51dc8346fedc75) (N (L 0xffffff70290326419ed0e3beb545e4) (L 0x1000000573c320b49f286920c7705a7))) (N (L 0xffffffcbca45de0e0bbec6e270e5f2) (N (L 0x10000001ed858ef94152044527f9230) (L 0xffffffee01b63a4180053132647b95)))) (N (N (L 0x10000000a5de113349f2555b64a97ba) (N (L 0xfffffffa197b5eef061c118dacc2a9) (L 0x100000003518db8cce6efe9a1af28b8))) (N (L 0xfffffffe27be9202247353039b103b) (N (L 0x1000000010386e837a504d05f4d1d0b) (L 0xffffffff72f92f31e3935cbb80f611))))) (N (N (N (L 0x1000000004bcac34880c799ce206113) (N (L 0xffffffffd7b4cd97bc0c667abccc6c) (L 0x1000000001531d87876eaafcc8be64a))) (N (L 0xfffffffff4f7ac5a54511cf9d40554) (N (L 0x10000000005af1ed8c27b02648ab142) (L 0xfffffffffd19d7cddd3b6957a307f9)))) (N (N (L 0x1000000000176c8513ca9aa812a60b9) (N (L 0xffffffffff4493eddc8e60833b3a0c) (L 0x100000000005cd490b59b45bc01b193))) (N (L 0xffffffffffd274240a782b7f503335) (N (L 0x100000000001623d2798c3caf7c8f3f) (L 0xfffffffffff55601908ab1ff0b4167)))))) (N (N (N (N (L 0x10000000000051723b1cde3b39ffa7e) (N (L 0xfffffffffffd9775084df0e11fcefe) (L 0x10000000000012128aa7353ac131500))) (N (L 0xffffffffffff798c56b1ee64dfc030) (N (L 0x10000000000003dfcf27809b26628ed) (L 0xffffffffffffe3a8b9280dedd965dd)))) (N (N (L 0x10000000000000cd9d8db3befd249df) (N (L 0xfffffffffffffa3855bbfbfd150581) (L 0x100000000000002942f76bfa4f66955))) (N (L 0xfffffffffffffedbc41b4fe50082bd) (N (L 0x100000000000000805a3697c9ecf4a3) (L 0xffffffffffffffc80f15053f0c7c63))))) (N (N (N (L 0x100000000000000183258066cc4ebad) (N (L 0xfffffffffffffff59cbe7afa40a84d) (L 0x100000000000000046d338f96335076))) (N (L 0xfffffffffffffffe209f8dce0013e2) (N (L 0x10000000000000000c9549820f35359) (L 0xffffffffffffffffac0bad37ef3bc4)))) (N (N (L 0x1000000000000000022c350fd989f3a) (N (L 0xfffffffffffffffff1b4a169a3cf24) (L 0x1000000000000000005d667b842886d))) (N (L 0xfffffffffffffffffda1da43d9bf46) (N (L 0x1000000000000000000f436c4d24008) (L 0xffffffffffffffffff9e423151fa4a)))))))

private def cneg_lf_175 : FastDTree := dleaf cneg_bt_175 0xfffffffffff95d0185701b36ba4ba7 0x1000000000001a6a8dc0cfcd4551e4f 0x10000000000009880727c3a30266965 0xfffffffffffff2c527cb1c4086d572 0x6d6c6be8173fa405db8 0x991359c1be30b59796 (M 0xfffffffffffa680703cd25c0990029 0x10000000000005f9801b616c5dbf332 0x1000000000000820a117ccefc680c7e 0x1000000000000001f723b61860cad31 0xffffffffffef4bfd3ecf8dff87595d 0x1000000000010e8af6d0116adf64a45 0xfffffffffffcaee4d8cd4caa83c95a 0x10000000000346403fa9845d42bd3bc 0x820a5559b221db4b2a (Q 0x59b292db37d5b5f6244 0x17c48de5d0853bd522d8 0x347ede2d57d1ff1e9aa0)) (M 0xfffffffffffc5dcab1ebc0d3a2eb57 0xfffffffffffef52839fb34688b5937 0x10000000000005a4c6958c6da6d21e1 0x10000000000000cd93ea396f5bf49ed 0xfffffffffff1cc57ec1dbe403eff93 0x1000000000006a6bf67c65ec63c8bf5 0xfffffffffff1997edd9cccb8c0d40a 0x100000000001ea4e975225d965aa26c 0x5b35891fd0450b3e6f (Q 0x3c7ba0310015b9dc206 0xfaea49d9274af2e8f97 0x21dbeda46d691876568b)) (M 0xfffffffffffde6c1da475310cbf5ff 0xfffffffffffe84470f0bf74afaac5f 0x10000000000003b9b6abc5376ea420a 0x10000000000000d1c508e4081904989 0xfffffffffff5b0fad3679500e0e715 0x10000000000010a869d34d77c87b66f 0xfffffffffff04edfeff492e7bffeb8 0x100000000000f54ebb3f8c68b2cfd69 0x3d08777d47863e8117 (Q 0x291e41f17fe94b2ec95 0xa5c722801a82eb0cffb 0x15f0411fa43d0a2de459)) (M 0xfffffffffffef4c836a5353fb9ba99 0xfffffffffffe920d2da1d2a07a983a 0x1000000000000261ca124c8a74f1560 0x100000000000006dd2ff058309c2f92 0xfffffffffff950eb122832ab15fab7 0xfffffffffffe7ca0badb15b07ab50b 0xfffffffffff30b341d3ba3da9f4ea1 0x1000000000005f8c365915e8634fb87 0x26b9e4b6eef3c5f06f (Q 0x1c520c3bf1ece7c865c 0x6da6237fa045be65bce 0xe4428b24b89884b1a91))

private def cneg_bt_177 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff02b58712c0d7331db2c52) (L 0x10000000081ce2457888f37d10057d5))) (N (L 0xfffffffd238a1a492df270c8576b2f) (N (L 0x10000000c76e632258b272aec6fbe0e) (L 0xffffffd362bfc47b3b8a4870a04b8a)))) (N (N (L 0x10000008868b6a71347f43560a9db5f) (N (L 0xfffffe92256f34cf6fbc7052fe5225) (L 0x10000036d6cabac4c1af298ad07b85c))) (N (L 0xfffff88ac99e3db74fe5011c141895) (N (L 0x100000ee4187134d803ec0db9b879d5) (L 0xffffe477ba993add50b0e2dfa76d4d))))) (N (N (N (L 0x100002f7d50fa43a6d341f586bf5abf) (N (L 0xffffb31beb6ab531b1cdf2b277f5c2) (L 0x1000075797272c90a06045a5a4ba462))) (N (L 0xffff55e2ac7faeed66f150a3b61de4) (N (L 0x10000ea64c8bbea8f3c195a1671b9ae) (L 0xfffecbab06654972eac67da3fe50d8)))) (N (N (L 0x10001845e8c44bd2b0a8515175058de) (N (L 0xfffe2a5c72af5f7d9fd474f3bbde53) (L 0x1000222805a24e0b0f094a5f03bf29a))) (N (L 0xfffd9ac021a73f4d460748834f2a98) (N (L 0x1000298d93fb3a18da5a7398125152a) (L 0xfffd466c7eb18001842a6d2385d5b3)))))) (N (N (N (N (L 0x10002c5729b2f1438c5f8498ea209df) (N (L 0xfffd43a1862cf761d9cfc22828157e) (L 0x10002a0036eaa38282f126061307549))) (N (L 0xfffd8c87181a7b05debd371f4e5183) (N (L 0x100023ac3f9962abd4c59bea29ec942) (L 0xfffe05b1ce24b408f2e0efc1614386)))) (N (N (L 0x10001b666d3f6a79041f310512decd7) (N (L 0xfffe8d2179a220dad719644793e97b) (L 0x1000132c5d2c42eb4d1b55c25ccb671))) (N (L 0xffff07b0865124d7df59e35b8de0b5) (N (L 0x10000c4d1e88237312930906cbcfe68) (L 0xffff67204515763ee400dcfbfc66a2))))) (N (N (N (L 0x10000746e11827edcc44bfaf16b44f6) (N (L 0xffffa8ffc8f8057114f62840c4b2f2) (L 0x100003fd1de0f8c1ab805e56e9cd0ac))) (N (L 0xffffd2047957f96d22b6fd0cb413d6) (N (L 0x10000208ecd5db27ab09d22bf1c9913) (L 0xffffe955d2334852cc2d506e4639db)))) (N (N (L 0x100000f84fdf928449f5555781ce494) (N (L 0xfffff58ae979d99fa07c4330f7b000) (L 0x1000006efd79a1d6a3cd31f7fa74e00))) (N (L 0xfffffb77da8aafa2f5a762118f0f00) (N (L 0x1000002eab4cbfdc5db093cd7088f82) (L 0xfffffe265623358a66330d4a843e40))))))) (N (N (N (N (N (L 0x100000128397443bf8ceee83b19369f) (N (L 0xffffff494c3e7cc44e65c73174caa2) (L 0x10000006f2a98ee2eae1a69f79636b7))) (N (L 0xffffffbd40747352ca1330fbadde81) (N (L 0x1000000278f97f312dd9a07ccb92a66) (L 0xffffffe8d94f22f16e2cb910116f8b)))) (N (N (L 0x10000000d6167d128b1f0a4f5eefa1a) (N (L 0xfffffff85c3dccc3c7028884bf0177) (L 0x1000000044f62eeeec853915fa19e5f))) (N (L 0xfffffffd98c048355f796e812d0262) (N (L 0x1000000015324946fa720599f7a948d) (L 0xffffffff47269a5839427fb0b73a1a))))) (N (N (N (L 0x10000000063a4962a30a64df98afbc7) (N (L 0xffffffffcade2ea0cb6ee66720201a) (L 0x1000000001c07dc322d4374b33fde30))) (N (L 0xfffffffff15dba70238037aeae420f) (N (L 0x100000000078fc31b489a0451e99080) (L 0xfffffffffc21d5267a9079486b592b)))) (N (N (L 0x10000000001f577cac56853a83a6e13) (N (L 0xffffffffff0481953147071979d676) (L 0x100000000007ceb68398a35c2c6bc62))) (N (L 0xffffffffffc28940a9e16b4586c5e3) (N (L 0x100000000001df6178fa2e405326ad3) (L 0xfffffffffff1874643c1cf6b9b14f9)))))) (N (N (N (N (L 0x1000000000006ed5257e4dde0eed145) (N (L 0xfffffffffffcb6b15ff3d0f13793e9) (L 0x10000000000018ba74ceb26bf941c64))) (N (L 0xffffffffffff4787c05ce3fdc1b0ca) (N (L 0x1000000000000554749465b0232af9f) (L 0xffffffffffffd8e7eac8bf150d17b1)))) (N (N (L 0x100000000000011c635aa04599ea25a) (N (L 0xfffffffffffff7fc079000000162dc) (L 0x10000000000000395f32115c93b582a))) (N (L 0xfffffffffffffe6899456a1ec4bd0c) (N (L 0x100000000000000b366fc52589f451e) (L 0xffffffffffffffb19b3a7120336049))))) (N (N (N (L 0x10000000000000021feeb4d3da1a6b1) (N (L 0xfffffffffffffff15e35f1ef78aef1) (L 0x1000000000000000640496fd7a8f963))) (N (L 0xfffffffffffffffd59503a013e3858) (N (L 0x100000000000000011dc1e6b993d9c5) (L 0xffffffffffffffff888a50486ddb21)))) (N (N (L 0x10000000000000000319699c20a36bc) (N (L 0xffffffffffffffffeb8f0a3db5f4eb) (L 0x10000000000000000085e4ff194da39))) (N (L 0xfffffffffffffffffc98ea3e42ad4c) (N (L 0x10000000000000000015fd0d47243ec) (L 0xffffffffffffffffff72d99b08a11e)))))))

private def cneg_lf_177 : FastDTree := dleaf cneg_bt_177 0xfffffffffff95af6d05887ab6bfa8a 0x100000000000190c480cd842e56a799 0x100000000000090c65e44050d10b06a 0xfffffffffffff1a178d8cbf7a98723 0x6d39ba439c813c5af31 0x917cbee174035f1d7a (M 0xfffffffffffa67ed032626e53b8536 0x10000000000004cfefd119ab86a43d6 0x10000000000007a7f405917518040a5 0xfffffffffffffea167067a4be56fd2 0xffffffffffef332f146dbd65fde88d 0x1000000000010b5973a1f01973316d5 0xfffffffffffc5183a0e4dbd3466465 0x100000000003445e371dc552f6f77b5 0x7a8176c3ca375d24a3 (Q 0x59a24c0c64e641c2518 0x17b1df8d59d9bcde50fc 0x346709be539e58e361f2)) (M 0xfffffffffffc5f86a6dcbb45400f22 0xfffffffffffee8619f299f20910095 0x1000000000000532b507b3a12422c26 0x10000000000000ad6ca298fc1ac29dc 0xfffffffffff1c647e588397f726ef2 0x10000000000067d41372743003b97c9 0xfffffffffff15fec1633aa880fb2da 0x100000000001e79218e2935e57a7c05 0x53dfa53d5a35a06691 (Q 0x3c9aa9a2dd29ae0d9dd 0xfa2bc6f71d11a8c7a50 0x21cd146299d0b96091b7)) (M 0xfffffffffffde881db8549676c699a 0xfffffffffffe7bfda850ce20f6eb8d 0x100000000000034e4afb1dc5eaaca41 0x10000000000000acb11571d537a2a81 0xfffffffffff5b59ef4cde7c561ff1b 0x1000000000000ec30b9e5490ebbfed0 0xfffffffffff031542568d773e7e9a0 0x100000000000f291ae10f7cd4749678 0x35fc047477ff69527d (Q 0x2954a6b0054dfe5a43a 0xa54f26e3a5f3f15a422 0x15e7021488a12c9f99ab)) (M 0xfffffffffffef599ddfb7318d1b421 0xfffffffffffe8ce70b35ca88c7bbf3 0x10000000000001fc61065db29db7f0d 0x100000000000004654dd4aa58f54799 0xfffffffffff95a6121f4e0f7d6380c 0xfffffffffffe68775b4be82dbba3d9 0xfffffffffff300c01656227bc88750 0x1000000000005d3e68d2062c861777f 0x2013d12127548a1724 (Q 0x1c8d17e829f4d795470 0x6d5be33777246ded0b9 0xe3e6b1ba731493a1595))

private def cneg_bt_179 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff005a5782da72cd3106975) (L 0x1000000008425b86df88318d96be0ba))) (N (L 0xfffffffd10407b19c79928206923a1) (N (L 0x10000000ce42dc954116b4a73617368) (L 0xffffffd184d6c07876f25183fda17e)))) (N (N (L 0x10000008f1d9f81c35fd8cdbf806755) (N (L 0xfffffe7d91616f8a02dbef7aad9a26) (L 0x1000003a4cdd2992e94ef14d50d670d))) (N (L 0xfffff80589228ed54675d1902b3ce2) (N (L 0x100001006f62cab57752c8f3929b275) (L 0xffffe2312cee5c7a4278a6279bfe10))))) (N (N (N (L 0x1000033b5a0dab757b4369ab15bd114) (N (L 0xffffabcf1d79ee442d285037f2eb87) (L 0x100008153d12fc93c82326f195abc71))) (N (L 0xffff43b9f23542c5c9de66ad1866d8) (N (L 0x1000104c2c278ba3abbcb1f539d33cb) (L 0xfffea73dfba6a8bae2348cc1963018)))) (N (N (L 0x10001b468cdef9cd2bd09cc04ac08f4) (N (L 0xfffdedb295989ae2ed8e1628a09aa8) (L 0x100026c0a94991e64207162f5388875))) (N (L 0xfffd44f760eed98b3fc57899e6ce3a) (N (L 0x10002f957307bb928180bdcb2ccdf25) (L 0xfffcdd912371b658ce9fec5491ddda)))))) (N (N (N (N (L 0x1000333b87c5dabde29a6e4841dee4c) (N (L 0xfffcd339e06969a3c6e0390ccc6641) (L 0x100030f3a814351f7f27202f900070b))) (N (L 0xfffd21946a3cd39d5fbaa605254f7d) (N (L 0x100029ed79c571aa93aac38e772a43f) (L 0xfffdaa7782813d4592a76012be78ef)))) (N (N (L 0x10002077f6a3c2c6f8db13417956d27) (N (L 0xfffe46c3af40e2363a76ddafe24493) (L 0x100016e6c233bc5816e6c14e2cfbd1d))) (N (L 0xfffed63fa23da6f08acfa18f1a551d) (N (L 0x10000eceb597d61facd87238e53485e) (L 0xffff474756a0d75bbb3f3f98cc73a6))))) (N (N (N (L 0x100008d370c49517c46a585d726ddf3) (N (L 0xffff9616045a891b62cb0aeff5ed48) (L 0x100004dfac43fd2e13e3734518f6097))) (N (L 0xffffc79c5d2288b8ae52761f6481ab) (N (L 0x100002811eac7c530caf02546361cfc) (L 0xffffe401a1681a8c00af9b322eaff8)))) (N (N (L 0x10000133c68407a93cac8db4aee5a48) (N (L 0xfffff2fe402185c88c4cadd97752d2) (L 0x1000008a869fb4a752ef856bbf2359b))) (N (L 0xfffffa531400e2284a65eb303aa3b4) (N (L 0x1000003aa504e33e367fdc31b0a481f) (L 0xfffffdaacb99a0964f16321f3219ef))))))) (N (N (N (N (N (L 0x100000176ba45ee2e5a77ee27d25901) (N (L 0xffffff181e339d40040fa5acbb3408) (L 0x10000008d8d09f179b64f2a59e97230))) (N (L 0xffffffaabb93c8b553984c17a7c36a) (N (L 0x100000032b2f96ad7d1fc5e92fd8a89) (L 0xffffffe23c81ccd2e9aab3ebf5ca44)))) (N (N (L 0x10000001141ad827259ddd75778f335) (N (L 0xfffffff61dcd865f794650ca02d650) (L 0x10000000597e69ef3e5609d9f7fb476))) (N (L 0xfffffffcdf1cb75a1924f7ae19c6c3) (N (L 0x100000001bad24f8d8049728e59808d) (L 0xffffffff0de8b56524b13fd45dccc9))))) (N (N (N (L 0x10000000082e44f0ad12336e1d7ab51) (N (L 0xffffffffb9ff27de85314c0771a712) (L 0x100000000250a77d6114e79c7f7a52f))) (N (L 0xffffffffec9af40bdd97bcd74507cc) (N (L 0x1000000000a0d05cd45d8e1a776302d) (L 0xfffffffffad80bb07e4ed9bebcf423)))) (N (N (L 0x100000000029e6a1ff7d55d7381c8ab) (N (L 0xfffffffffeaed07c9b829d41df40c6) (L 0x10000000000a7f5b2af1b6d92b0b321))) (N (L 0xffffffffffad20325d92e13be6c66d) (N (L 0x100000000002882eac5fdc235b8a5c8) (L 0xffffffffffec60c9562b8fbde8efc7)))))) (N (N (N (N (L 0x10000000000096b187430111a45e094) (N (L 0xfffffffffffb84f80971c1bf8dcf03) (L 0x10000000000021ce7fc53968a8403d2))) (N (L 0xffffffffffff031f3c77fc2625b6ed) (N (L 0x1000000000000753800d7b73ac1bec5) (L 0xffffffffffffca1e8816dc81e4af82)))) (N (N (L 0x1000000000000188ffdae98b11b3e0d) (N (L 0xfffffffffffff4e4d4a29ec9ceff1f) (L 0x100000000000004fb3fbe16408d9402))) (N (L 0xfffffffffffffdc889db349f005b0d) (N (L 0x100000000000000fa89b4b8ed7afc27) (L 0xffffffffffffff923cf6dea9da0345))))) (N (N (N (L 0x1000000000000002fb8b75f009c4e5c) (N (L 0xffffffffffffffeb685c602a62916c) (L 0x10000000000000008d1e9616e3f8807))) (N (L 0xfffffffffffffffc3ffb797b452681) (N (L 0x10000000000000001953b17eb7df2a3) (L 0xffffffffffffffff562b64435218e8)))) (N (N (L 0x1000000000000000046ac6defb404cd) (N (L 0xffffffffffffffffe2cb6a107239e8) (L 0x100000000000000000bfc6518ac9016))) (N (L 0xfffffffffffffffffb1d4a9000e169) (N (L 0x1000000000000000001fa60289a8766) (L 0xffffffffffffffffff34585570cce1)))))))

private def cneg_lf_179 : FastDTree := dleaf cneg_bt_179 0xfffffffffff958d03dfcbf12d6f92d 0x10000000000017c0790bc3c4d23288f 0x100000000000088d9e98de47dae0c3d 0xfffffffffffff14c1eb82c6c9c8ba4 0x6d11171f02d6bc1c974 0x89a3cb5b39df785321 (M 0xfffffffffffa67a9fe8cf51eae3410 0x10000000000003b8666d5e8b9dc9ddb 0x100000000000072c269204e0af15a3c 0xfffffffffffffdf3c5c46d45c50aba 0xffffffffffef1b1f63731b29c226f6 0x100000000001082f52b175e55239424 0xfffffffffffbf558e16b9aadcb36d5 0x1000000000034276f9170dbccf29b08 0x72c757835a2d6d66eb (Q 0x59992c4966a0a50ed84 0x179f75561774f0ebc792 0x344f77671f0eee6b619d)) (M 0xfffffffffffc610655ab6ff730d8c0 0xfffffffffffedcabddeb9ec2902514 0x10000000000004bd85506f6563aa4ee 0x100000000000009a7f60f28cf0c33f8 0xfffffffffff1c0b00d6dba58a7d0be 0x10000000000065442ae8eb18eda7d1a 0xfffffffffff127538f32e9ccf16490 0x100000000001e4d5a8b8da57305a380 0x4c75561125bfaed8a6 (Q 0x3cbad88e16aaa7b93fa 0xf9701eee5ae29da4b04 0x21be624fd4d5f53e8731)) (M 0xfffffffffffde9fa244501cd910154 0xfffffffffffe74b5766d5518c94329 0x10000000000002dfbc36f8c6aabd3a7 0x1000000000000094f85b0a3bfda8e5d 0xfffffffffff5ba84b72d9667734819 0x1000000000000ce5368aa4a5499c50a 0xfffffffffff01482d8ea14200ade53 0x100000000000efd7cbcb955378e10d7 0x2eeaf08971ed8c042b (Q 0x2986853828cb1296b87 0xa4d90a57758d57d9016 0x15ddd9cd6e369d109813)) (M 0xfffffffffffef61e3248a23e6b15bc 0xfffffffffffe88b3fcb089109b7eb5 0x1000000000000193cd4cbe0b6064208 0x100000000000002c43f51a355a09fcc 0xfffffffffff963f1a6b71b712dfc93 0xfffffffffffe54b681a0d3103fdffe 0xfffffffffff2f6cc62c8d89f244e6d 0x1000000000005af53b0e6f2d4bab175 0x1963cf8a721ad2083d (Q 0x1cbeff13aaaf69f21f6 0x6d12c87168fe591e150 0xe38ba5ecce99f393471))

private def cneg_bt_181 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xffffffffefdff27f2f40e67445a699) (L 0x1000000008682d9bd81347e56114c0c))) (N (L 0xfffffffcfc9e27b193e074acc8db8b) (N (L 0x10000000d545305ee0072a13f9b282c) (L 0xffffffcf96a021ad076247b347656d)))) (N (N (L 0x1000000961a1b220ffbf27b6a52c360) (N (L 0xfffffe67fb401d9247a33010a30632) (L 0x1000003df49a1fc517f2a4ebfd04e28))) (N (L 0xfffff777e6d94692a428af3daf6429) (N (L 0x10000113e0ff242230c7c9e6f14a886) (L 0xffffdfbe50558f774917ee2532d989))))) (N (N (N (L 0x100003846f44ecf90a775da6cf63448) (N (L 0xffffa3dcbf5b08cc9df555e30df3e5) (L 0x100008e4d6bcee2e13fe069799ec6b6))) (N (L 0xffff2fbd85379a6a0f10a4dbe45bcf) (N (L 0x1000121ef3c250ab088bf744704c90f) (L 0xfffe7ebaddc5009f8ffa7c1ca1e5e8)))) (N (N (L 0x10001ea1c031757c79ed7d2072bb455) (N (L 0xfffda98cdaf318693fc904fccfe2d5) (L 0x10002bf0e381ca1715e86950082611e))) (N (L 0xfffce3ab1c649dd5f762dc055cb9c0) (N (L 0x10003674bc3a506ba28fe3d3ee61fb7) (L 0xfffc6587aac2bf9a75b9150dc13a89)))))) (N (N (N (N (L 0x10003b28749a6112b32c69c73e3a4d0) (N (L 0xfffc516461ecab12d135c73599285a) (L 0x100039040064eea27f58ce085572a63))) (N (L 0xfffca4f97115f98bb1ad6ba2891734) (N (L 0x1000313efb050e38cca677988d8f14c) (L 0xfffd3f47cedcefa31429270c39853a)))) (N (N (L 0x10002672c261ac1298cd7477556b85c) (N (L 0xfffdf369392dc94e65143716651325) (L 0x10001b55d42446dd4b0d1cd14fcb042))) (N (L 0xfffe9b3727e2d1b1654ce72d696306) (N (L 0x100011cfc41f841b67db75eaa0cfbd5) (L 0xffff20f4f6999c52dcc051d2951cef))))) (N (N (N (L 0x10000ab27005d1deb19f53a2e45aacf) (N (L 0xffff7f27bff528de38bbc2ad69d88f) (L 0x100005f3605ad9ce9ecec851e028597))) (N (L 0xffffbae66685f2d1c34a5a3de9ef74) (N (L 0x1000031475dacb6a081e08c325eaebc) (L 0xffffdd73529ac100d92a6d239b3d7d)))) (N (N (L 0x1000017d30f777bea0617096657997a) (N (L 0xffffefd59c90de702cf55de308405d) (L 0x100000acc2e05047bcf998090f8429a))) (N (L 0xfffff8e5cfd975a7640d224857621a) (N (L 0x10000049a2e0df49ab0e67b9d170cb8) (L 0xfffffd0f9d7c92a47c442efa361f02))))))) (N (N (N (N (N (L 0x1000001d9aa8e6d16bf2aa821f74931) (N (L 0xfffffed9ee15ce87ba530dcf8b8dc6) (L 0x1000000b4194494e71da835de3cb13d))) (N (L 0xffffff93295e7adb917d50dc690b13) (N (L 0x100000040ebf686f2c33dc532b0a466) (L 0xffffffd9c3fff85cedf8c82f4aea70)))) (N (N (L 0x1000000163cd636924c2d6bc15f3460) (N (L 0xfffffff339450a8b0b37ea6faab513) (L 0x10000000740ba32f8bdece1a3261ccf))) (N (L 0xfffffffbee4dc57ed1e98ac4ae3525) (N (L 0x10000000241b9dfa9431dae2721b8bc) (L 0xfffffffec3331f7ce016ccc2311a56))))) (N (N (N (L 0x100000000abccd1fbd4f0f141be3304) (N (L 0xffffffffa3d8121fb428a26c4842df) (L 0x10000000030e831f7c3ef6114b5cd34))) (N (L 0xffffffffe6511c143f6692f911b88c) (N (L 0x1000000000d593cdef56d212e4ec600) (L 0xfffffffff921e1c49b466ae3ff2c34)))) (N (N (L 0x100000000037f885d576f898fbbb33d) (N (L 0xfffffffffe3c4d84f3b530f2aae4eb) (L 0x10000000000e1a3c7ef565fe922e3d3))) (N (L 0xffffffffff9059ecb89f9cf04234b4) (N (L 0x1000000000036baf0f10025240df3ce) (L 0xffffffffffe56ad128a9fb662fe594)))))) (N (N (N (N (L 0x100000000000ccb76ed4a78055c467b) (N (L 0xfffffffffff9e57a14e90ccbd0c78b) (L 0x1000000000002e2da98e28478468ad2))) (N (L 0xfffffffffffea5a44074344b109e88) (N (L 0x1000000000000a0fbe8b47fa1940836) (L 0xffffffffffffb5cdb5ffbb0ab49840)))) (N (N (L 0x100000000000021e9f974840cc5cb65) (N (L 0xfffffffffffff09ff589faf98aac11) (L 0x100000000000006ea172adc27168dfb))) (N (L 0xfffffffffffffcea474b90e5bd01bf) (N (L 0x1000000000000015d937847c8f5b94e) (L 0xffffffffffffff6673b9e1b7fbb611))))) (N (N (N (L 0x10000000000000042ee40beae7d4147) (N (L 0xffffffffffffffe30b6ff7689e73b7) (L 0x1000000000000000c6efe246acb01da))) (N (L 0xfffffffffffffffab339720e733336) (N (L 0x100000000000000023e2675ecc2c558) (L 0xffffffffffffffff0ec5b108f42ede)))) (N (N (L 0x1000000000000000064a2b377675811) (N (L 0xffffffffffffffffd64f4758aab18c) (L 0x100000000000000001126ea2087461a))) (N (L 0xfffffffffffffffff8fdd17f34b52c) (N (L 0x1000000000000000002d8306bf716bc) (L 0xfffffffffffffffffeda6c3bfd6ab1)))))))

private def cneg_lf_181 : FastDTree := dleaf cneg_bt_181 0xfffffffffff956acaddc33345280ed 0x10000000000016876f87022ed61a39c 0x100000000000080dd08e12438641683 0xfffffffffffff1cadb55921400dc1d 0x6cf013aec52a78c7766 0x81a5354546ec3bb067 (M 0xfffffffffffa675d20ba37e0246514 0x10000000000002b3320998808b8a607 0x10000000000006af560a779412cb584 0xfffffffffffffe1c24bd804df0227f 0xffffffffffef03c9d9b3c3aa031087 0x100000000001050c9ad6da06d7a132a 0xfffffffffffb9a5e9a7feab27a6345 0x100000000003408ac2600afa02c4b0d 0x6af9e81e8ec467c236 (Q 0x59949d486260c4d0302 0x178d4e07bac6fdeb24f4 0x343825f1a2a50413851d)) (M 0xfffffffffffc62695c357d61f03d16 0xfffffffffffed20bd6c5817cc07c89 0x1000000000000447512bfea6c640a1c 0x1000000000000095209795885405af0 0xfffffffffff1bb8d7bf9efc681e8c7 0x10000000000062bc384c75fea3cb601 0xfffffffffff0efb0007e63b1e06c78 0x100000000001e21966dc62b24da1882 0x451709c7a60bdc1e56 (Q 0x3cd9900d8baf37799f2 0xf8b739d47aecab7029a 0x21afd6d59abb031b654c)) (M 0xfffffffffffdeb4a9b64509a4cfa11 0xfffffffffffe6e73692fb3ec94d0b9 0x100000000000027020eaf9ecce65f90 0x100000000000008aeafa0776d77ebed 0xfffffffffff5bfaa68e030ecafe393 0x1000000000000b0ee0bc3004a6e50e8 0xffffffffffeff867a4f7b5f6bec4fb 0x100000000000ed211ff628b03776dd5 0x27f6ba2b30a52b0be1 (Q 0x29b1984986d912fc29f 0xa464af6cb8a5ac2110c 0x15d4c80c4872d50e944e)) (M 0xfffffffffffef67540437a5e65baaf 0xfffffffffffe8579073853e2e7b0a6 0x100000000000012a227c8a542ad1805 0x100000000000001feca1d35ec5c557e 0xfffffffffff96d9beac0518653e5d1 0xfffffffffffe415d7f13317fa4dbf2 0xfffffffffff2ed558753c2a4010012 0x10000000000058b0ab173cca4fbc64e 0x12bdb34d4b1631c914 (Q 0x1ce61ab6ee3bdda53cd 0x6ccab14f56f5da7ac09 0xe331669f0c3eeba9e3f))

private def cneg_bt_183 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xffffffffefba3f8630daa0157ae3bc) (L 0x10000000088e5884622a36846f099da))) (N (L 0xfffffffce8a24ec5ba2e18190151b1) (N (L 0x10000000dc763076c359cbf9562d385) (L 0xffffffcd97aee74e1587de40e43544)))) (N (N (L 0x10000009d609825bfd7a4ca8cdc9741) (N (L 0xfffffe51585359112e3d66508862e8) (L 0x10000041d06e3fedc0a3681bdca5c3c))) (N (L 0xfffff6e16ae64817b7d8a71f1d3b81) (N (L 0x10000128aaa82345d4bcd01f14ec880) (L 0xffffdd1c1249f9fba0a96df7863bb9))))) (N (N (N (L 0x100003d380b0c35decc4b29fd2f4713) (N (L 0xffff9b373783e8c05c40b0b4d29908) (L 0x100009c7fa12041ff77c1ecd0bea814))) (N (L 0xffff19c141223cc61e882e6eb57162) (N (L 0x10001423249e0d681acedffd22dac70) (L 0xfffe51b2a3b7f4937f14641ebe7262)))) (N (N (L 0x10002261a43726c948e8fdd59a1a182) (N (L 0xfffd5d0a26900b71078155cd14bf0a) (L 0x100031cb5af5bc91b7b9070a87f5a57))) (N (L 0xfffc75609751cf9fbb458743fdac33) (N (L 0x10003e48460e040104c74753603702c) (L 0xfffbdc333b7dd699e49876ddc34885)))))) (N (N (N (N (L 0x100044442477386d46b5133ba7b0796) (N (L 0xfffbbb85a9573ff907bc18c3968f29) (L 0x1000425d5168f27c1003cf3c84ebaa5))) (N (L 0xfffc13e42d25ca64bc7ec4585b28bb) (N (L 0x100039cd9c3d39567c1550762646d80) (L 0xfffcc16da183e1f22dc388b56c14cf)))) (N (N (L 0x10002d7f863f463d5164eac391a4a75) (N (L 0xfffd90bdc77187918bbc710d6be364) (L 0x1000209ad83ffb3c7d270014ea146f4))) (N (L 0xfffe54c744008f51c173d37b35046b) (N (L 0x10001568f70218cf0bab9941fc4f42f) (L 0xfffef2e0937d429748ac9e8fd98797))))) (N (N (N (L 0x10000cf497cb3558ef34ce1ad47d87a) (N (L 0xffff635fa4363bfa7405cb3f8d7a53) (L 0x10000742a5189c375887b2f45bab0c2))) (N (L 0xffffab62e54a38818db70516deb15d) (N (L 0x100003c8f1cc98d60f6d64a286b3c97) (L 0xffffd56419f42925d0fb4724f4c023)))) (N (N (L 0x100001d7c3faad71771cb94096a7e14) (N (L 0xffffebec78b5c234f63fe11730ea0f) (L 0x100000d74b4aa880302f74814ea2ae3))) (N (L 0xfffff71e73ef8779b0a99297396b51) (N (L 0x1000005c63ad9f29d03781212ffbc24) (L 0xfffffc4cd7d73dd29a236837c9d4d5))))))) (N (N (N (N (N (L 0x1000002564376325e21ff9a3ecb5d51) (N (L 0xfffffe8b5ab7d5b884a3208b784fa9) (L 0x1000000e4f6f7c3424d028a8b5358eb))) (N (L 0xffffff752f065722981e0813f5e443) (N (L 0x100000053118ed1315c68370688578e) (L 0xffffffceec4dcebcf424b15341456e)))) (N (N (L 0x10000001ca23a9f3843e5b60ae3ae14) (N (L 0xffffffef7f60e5191f280842ded6c6) (L 0x10000000965a98232e6ab4fc489ee42))) (N (L 0xfffffffab62e77112b2f50a7d0a5cd) (N (L 0x100000002f11e93d39ed0fee87e3b4e) (L 0xfffffffe61c58430d3e3f00069ece8))))) (N (N (N (L 0x100000000e14f55edbb20a7a627f421) (N (L 0xffffffff86c7beeaf95ec164c56dad) (L 0x1000000004085819d3e8b43835f453e))) (N (L 0xffffffffde04764feb7ec94b8ec8f1) (N (L 0x10000000011b6b209de5ff693fb829e) (L 0xfffffffff6dc350ecadb34962dbb5a)))) (N (N (L 0x10000000004ab3fda6f36b1e274a35c) (N (L 0xfffffffffda367f48863edab9c21a9) (L 0x100000000012edfecf92ba8ab6e2ba9))) (N (L 0xffffffffff69b64cd8466b24aa90dd) (N (L 0x1000000000049e0a5fd7eb7cf273ec2) (L 0xffffffffffdc0477d28100670aa1e0)))))) (N (N (N (N (L 0x10000000000115df279b49828a8aeda) (N (L 0xfffffffffff7b148844316969e6389) (L 0x1000000000003f0627048d06b11e9d5))) (N (L 0xfffffffffffe260232fc45cff943b3) (N (L 0x1000000000000dce6a38325d1125728) (L 0xffffffffffff99ea4d8a047d3730cf)))) (N (N (L 0x10000000000002ec91f3101d0bcd19e) (N (L 0xffffffffffffeabbb041b729d79a84) (L 0x10000000000000996d4be471052792b))) (N (L 0xfffffffffffffbb5e9fe134ad1c87f) (N (L 0x100000000000001e75790b157a60059) (L 0xffffffffffffff296299d4edd1d022))))) (N (N (N (L 0x1000000000000005dca561d59ed2b53) (N (L 0xffffffffffffffd7521e09385e4352) (L 0x10000000000000011832b7773497824))) (N (L 0xfffffffffffffff8842b9a4902a336) (N (L 0x100000000000000032cc540b0d6377d) (L 0xfffffffffffffffea9a8fd7cdc680b)))) (N (N (L 0x100000000000000008f2c839ff7cf69) (N (L 0xffffffffffffffffc48a43a17d48a2) (L 0x100000000000000001885e94ad75b38))) (N (L 0xfffffffffffffffff5f47718d309c6) (N (L 0x1000000000000000004163d0ebbc5b6) (L 0xfffffffffffffffffe592bef7c3afd)))))))

private def cneg_lf_183 : FastDTree := dleaf cneg_bt_183 0xfffffffffff954ab75d3685d86f1ac 0x10000000000015612a0885eb0757ed6 0x100000000000078f1c4631217d98eba 0xfffffffffffff31e35e8bd985060d7 0x6cd428daa6f1bb63cab 0x79a12c65de5cd07a52 (M 0xfffffffffffa672604c757be82f764 0x10000000000001c050cc31042b764df 0x1000000000000633a0df62dd84adf96 0xffffffffffffff1ae5870a53780b38 0xffffffffffeeed2a81973fc490d799 0x10000000000101f14e4e7f23afcbe97 0xfffffffffffb408efeca48a6ea6cb7 0x1000000000033e99cd2ccfce083575a 0x633b5704a226c5557c (Q 0x599205d60792c58c8da 0x177b681411f84b2a13b1 0x3421142e4e5b1ac78118)) (M 0xfffffffffffc63cfbdeb80d8e8090a 0xfffffffffffec88173b124d1a9c63d 0x10000000000003d23348d3475a1f896 0x100000000000009d5226f922e4d8c2a 0xfffffffffff1b6dd99d18762f50492 0x100000000000603c32f6ed8ed1d01d0 0xfffffffffff0b8fc50018e074be2d4 0x100000000001df5d7199d7e1340ee96 0x3dec9c6de75441d163 (Q 0x3cf45a3a3ac3fd226ce 0xf800fb0367263ca4111 0x21a1715c0d21eea88551)) (M 0xfffffffffffdec9383f5c9e0f0bf00 0xfffffffffffe693781a190bb7c43a7 0x10000000000002019060d9d10fb9326 0x100000000000008e8731c244a25b29a 0xfffffffffff5c50e9de632fb8418f5 0x100000000000093ffc9cd5558471862 0xffffffffffefdcfe4c7c9b56d3afc0 0x100000000000ea6db5040655b71b79a 0x214fe7e166ecdd2d12 (Q 0x29d3e1892c93fd755e0 0xa3f1f552803e141b1cf 0x15cbcc8d548e8e730afc)) (M 0xfffffffffffef6bf68bc5243ff188c 0xfffffffffffe8336486941b0550781 0x10000000000000c174b52c0ec219dab 0x10000000000000214a0704d6e64eec4 0xfffffffffff9775f74acedc04b640a 0xfffffffffffe2e6b6c874405d3b62f 0xfffffffffff2e4582b27ca7a40804b 0x1000000000005670b65bce50a67f888 0xc45132e3f58410a2b (Q 0x1d011854fec97f6fa24 0x6c837a5b86951166f05 0xe2d7f23b97a06377a0f))

private def cneg_bt_185 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xffffffffef948c8d327459b6b020df) (L 0x1000000008b4dc407dccfd6ac09ca1b))) (N (L 0xfffffffcd44c1f0b61e7d4109d4562) (N (L 0x10000000e3d6b0c19b13299b039c5bd) (L 0xffffffcb87941f92b6ef636f9f0530)))) (N (N (L 0x1000000a4f3955c7565b500f2b318f0) (N (L 0xfffffe399d865bbcfd18a440c02279) (L 0x10000045e2dfdaba98e6a05b439d6aa))) (N (L 0xfffff64197990a5723850ae70db30d) (N (L 0x1000013ee1cb07e5f63856183c544a1) (L 0xffffda472f21e36cc7df6b383468aa))))) (N (N (N (L 0x1000042901c319f925dbf202737a9f5) (N (L 0xffff91cfe5493b0851b85cd72e93ac) (L 0x10000ac05e3cfa853c30b721642d443))) (N (L 0xffff01951e70720714d6ebc6dd92af) (N (L 0x1000165dac83a7fd2636e4ae8901454) (L 0xfffe1fab291bd0df3538a80ef88bd3)))) (N (N (L 0x100026916cede997619b5c9a77212da) (N (L 0xfffd07303f3e457d863b61b671f80f) (L 0x10003864e5ce68cb9d294db09cf312c))) (N (L 0xfffbf86e9b6f0e6eaa413f771ed3ea) (N (L 0x10004730991c72c4d2fc8614aec9fb7) (L 0xfffb3f2ec4cd1870ed897dd5f45e5b)))))) (N (N (N (N (L 0x10004eba1959bb61552666924e78f0a) (N (L 0xfffb0ea232f06f379dd60b2b67fb80) (L 0x10004d323ff426a8e881afdb0dc5428))) (N (L 0xfffb6b1336cc4329bb8abea3084d43) (N (L 0x100043cd5bb2dfdc5ae3a0d11b57f35) (L 0xfffc2dc205e1b0739610bc790bcf2b)))) (N (N (L 0x100035cddbe1610bdc48a19d7fc4bdb) (N (L 0xfffd1c053503a1da9907845b6b1599) (L 0x100026dd07f3727ace83feeaff1e5cf))) (N (L 0xfffe00caeb6c92a09ceb64f7dc30b6) (N (L 0x100019b7a1a3b17fc5d1ab6dac48568) (L 0xfffebb8224d9d72eac3b01d38404b7))))) (N (N (N (L 0x10000fadefcdd42a76a2ea4887dc218) (N (L 0xffff41bd2a94879e78c18f3489d081) (L 0x100008da0d757df8cf03e5567bd46d7))) (N (L 0xffff987726ffb7bdb137b4cb52f15a) (N (L 0x100004a5dd9be26ad999375b51a61ac) (L 0xffffcb7d8f9984ac0274b968f8f5aa)))) (N (N (L 0x100002476ce814d0cb8dccecc5c9909) (N (L 0xffffe715ee60ed474a34c1a556db19) (L 0x1000010c188527763c9e0bc30af974a))) (N (L 0xfffff4e7358d36416aef709e6efa8a) (N (L 0x10000073d474cd1ae8e7942dfb60ceb) (L 0xfffffb58909bb6d18a7a5b6087b640))))))) (N (N (N (N (N (L 0x1000002f30d99c10f77af67cd26afd6) (N (L 0xfffffe282637c3502450a53d45725d) (L 0x100000122dcdfef223bb8a02317891c))) (N (L 0xffffff4f165cbd103f016e38ba7140) (N (L 0x10000006a344c5e2074e2e2898b4b8b) (L 0xffffffc10e33d806703eb660f575e2)))) (N (N (L 0x100000024d7173414ba035d974911fb) (N (L 0xffffffeab3a23ed335f41c1ab67b8c) (L 0x10000000c2a657b2ff7b6143c48ba0f))) (N (L 0xfffffff921f3388e63ee5f7c101ed0) (N (L 0x100000003d4f860f4037f51462266c6) (L 0xfffffffde2d180fa88bb38fca89007))))) (N (N (N (L 0x100000001273f18e8eb4d3585b7aa57) (N (L 0xffffffff60ae27b0a55cbcc1cd8b65) (L 0x100000000550d3bac7a6406468e6d3f))) (N (L 0xffffffffd312add4f017981bff3aa2) (N (L 0x100000000177c9ebf6bd8b40df66eb4) (L 0xfffffffff3d8a76cec6a0709b6287d)))) (N (N (L 0x1000000000639f488060af873f79692) (N (L 0xfffffffffcd76d2b27d4df972ec0e7) (L 0x1000000000196354baa5905083f3986))) (N (L 0xffffffffff35dea4731967570eb23c) (N (L 0x1000000000063a3d5ddf3f589e74472) (L 0xffffffffffcf55b0aee296cf1fecd1)))))) (N (N (N (N (L 0x10000000000178d9e9a26a0a9f66da2) (N (L 0xfffffffffff4b3d09a735ea2664e74) (L 0x10000000000055f12f1b37a7daa2fd8))) (N (L 0xfffffffffffd77e4a83c42d408687a) (N (L 0x10000000000012edc4fca9e090dc492) (L 0xffffffffffff73aa0e2c48057ba2fe)))) (N (N (L 0x1000000000000407cc8a0bb8026f07d) (N (L 0xffffffffffffe29be869e698d6a995) (L 0x10000000000000d4988601bc89879f4))) (N (L 0xfffffffffffffa0a74b01e19e0cf6d) (N (L 0x100000000000002a6d09ac549d85700) (L 0xfffffffffffffed44a78ea263347c8))))) (N (N (N (L 0x1000000000000008350b0822c318f9d) (N (L 0xffffffffffffffc6e64618a732ec9b) (L 0x10000000000000018a4f21784cdccd8))) (N (L 0xfffffffffffffff5711e3df96592f1) (N (L 0x100000000000000047d8ed7f37baefc) (L 0xfffffffffffffffe1a976369493b03)))) (N (N (L 0x10000000000000000cb83b3392ebe29) (N (L 0xffffffffffffffffab456697521e08) (L 0x100000000000000002307f257a23bbd))) (N (L 0xfffffffffffffffff19d9014045fad) (N (L 0x1000000000000000005dddfb73b2b10) (L 0xfffffffffffffffffd9f8e03e4acd4)))))))

private def cneg_lf_185 : FastDTree := dleaf cneg_bt_185 0xfffffffffff952eb9e67616d886dd3 0x100000000000144d57955e70b06d946 0x10000000000007139731609c89bfdf1 0xfffffffffffff541934e5b44d222af 0x6cbac963183db754c88 0x71bbec5d1e08f990fa (M 0xfffffffffffa6723f35d927a6246c5 0x10000000000000df71a5af03ecbe07c 0x10000000000005bb1a63c1c186732b4 0x100000000000000eb4d68f297179abe 0xffffffffffeed73db40984ffd7d98e 0x100000000000fedd6a8f41530e19bb1 0xfffffffffffae7e470cd8a3396946d 0x1000000000033ca45132552c92bbc32 0x5bb314c76b711802f2 (Q 0x598edb93ce340b9f9c9 0x1769c19e869a0ba082ac 0x340a40f32a66007b63d6)) (M 0xfffffffffffc655922b79390b14032 0xfffffffffffec007b4483a13803a2e 0x10000000000003603b1dc814ad56be2 0x10000000000000b2c4e5d09028d90e5 0xfffffffffff1b29e12a842836e353b 0x1000000000005dc40e00e9c57dec3f7 0xfffffffffff083338f38231e141659 0x100000000001dca1e591e1b793ad8c3 0x3728b9447147a1f8b2 (Q 0x3d08f5fa322b073b288 0xf74d41ddd5b30447f77 0x21933149b3b29139ea5d)) (M 0xfffffffffffdedf4bdcaf0cf24a6de 0xfffffffffffe64fcde924373303c36 0x1000000000000196168d76404a63191 0x100000000000009f7aeaa70028cceff 0xfffffffffff5cab023132be1e68d7d 0x100000000000077878ab2770cbe4196 0xffffffffffefc242b89667518adf19 0x100000000000e7bd945cf8e96c39749 0x1b44d391e86a858a6e (Q 0x29ebb073d958236a2b4 0xa380b8ccb9440f04849 0x15c2e707645d882c451b)) (M 0xfffffffffffef71ca2b93ce9ce06e6 0xfffffffffffe81e703436117b30f2d 0x100000000000005bcca22db60818990 0x1000000000000030079cb9cbe4ded94 0xfffffffffff9813bfb16a8843aee24 0xfffffffffffe1bdf2763e9a8b18ce8 0xfffffffffff2dbd115edfb46612a30 0x100000000000543559b4b497bd51d95 0x67a04102072b34533 (Q 0x1d0efa3e98c65ee38c8 0x6c3cff9512d9b7a04f7 0xe27f46bf3576322045b))

private def cneg_sub_19 : FastDTree := (dsplit (dsplit (dsplit cneg_lf_171 cneg_lf_173) (dsplit cneg_lf_175 cneg_lf_177)) (dsplit (dsplit cneg_lf_179 cneg_lf_181) (dsplit cneg_lf_183 cneg_lf_185)))

private def cneg_node_20 : FastDTree := dsplit cneg_sub_18 cneg_sub_19

private def cneg_bt_189 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xffffffffef6ed994340e1357e55e03) (L 0x1000000008dbb8d02afb9c9855cdcc8))) (N (L 0xfffffffcbf9ac737b2736a3f2775e5) (N (L 0x10000000eb6787113966687c2dcaac0) (L 0xffffffc965dee32a02e18c277a6a45)))) (N (N (L 0x1000000acd5a211348ac10aeab9c7d4) (N (L 0xfffffe20bf6516ea608dd0593cd787) (L 0x1000004a2e8fcc9e09232155ca44528))) (N (L 0xfffff597e92f12278f2589212335b7) (N (L 0x100001569d04526019cae95d6bfac32) (L 0xffffd73c2f54cf071c75112763cf89))))) (N (N (N (L 0x100004856ddb678a5eb0ca65564ea29) (N (L 0xffff87970ebde33221652fdda51cc3) (L 0x10000bcfde2766f556fa78977c0618d))) (N (L 0xfffee704e13fc6e15d7dbd474491b0) (N (L 0x100018d3ef4a2fbb51cbe2578fcbe74) (L 0xfffde81e236785403b4743053f19c4)))) (N (N (L 0x10002b3d7c377382dfd73684fac3da4) (N (L 0xfffca6e9283798111f82446962fcbc) (L 0x10003fd4c7f1c918584cb725cd26aed))) (N (L 0xfffb6af80a834444fc5bbdfd377251) (N (L 0x1000515263e7fa0421ba6ce7f29b1ab) (L 0xfffa8bc3c3077d53b3fbf7ac63bd26)))))) (N (N (N (N (L 0x10005abbd7c8f2bdceea229e1becaf7) (N (L 0xfffa475108da7e5a1bddd3f91403d6) (L 0x100059bcf6000d44829b4ce1a7d3ff8))) (N (L 0xfffaa6c5295da9f5389b6f35826b81) (N (L 0x10004f7a76a2e099eadde03153598ed) (L 0xfffb809a0a114216863b18e9e49caa)))) (N (N (L 0x10003f9561f3a0f98d844733757b96a) (N (L 0xfffc9209ff7cea31e51aa315101c48) (L 0x10002e4a999dddbf04d534ed1d8f391))) (N (L 0xfffd9cb8a4027c7067a97638888d1e) (N (L 0x10001ede9826771021123aefa5a8a88) (L 0xfffe79063c2cc79287cd7aa4f6a204))))) (N (N (N (L 0x100012f671c3c2b2f0472e661562970) (N (L 0xffff190c179d7748e6e3bd67381f88) (L 0x10000ac8c3ed9f493e71957b2bbc038))) (N (L 0xffff8167e2eb41f22ebcbc08875c26) (N (L 0x100005b41612ed307ae1515288994fd) (L 0xffffbf565245bc4a03676330c2a9af)))) (N (N (L 0x100002d0fa51902489f78afacceae07) (N (L 0xffffe11ad6066d59ac342d56ed60b8) (L 0x1000014d98ad8e443042b07780fb251))) (N (L 0xfffff2251f49b3ac0669333d800a60) (N (L 0x100000911b78905299b3026f501d60c) (L 0xfffffa266e346a4601c2a2656d07e2))))))) (N (N (N (N (N (L 0x1000003b8339a05d08f34636165f6a5) (N (L 0xfffffdaafebc801ac12f8ccaa4c08f) (L 0x1000001713532f0aa48a1804a8c99e0))) (N (L 0xffffff1eb62cabe72ba492ada5b25b) (N (L 0x100000087ad658b044f7a56ea3e8fe7) (L 0xffffffaf55336ef3d622c17dd3dce5)))) (N (N (L 0x10000002f5c7c398ea1336fe0950f12) (N (L 0xffffffe488aa21d72f09dba0f5a64a) (L 0x10000000fbcb8e8566a815125438c1e))) (N (L 0xfffffff716d856a9543b1ec7ae0617) (N (L 0x100000004fcbb0b6040655f39a08c78) (L 0xfffffffd3d8696e67fb384967a5fae))))) (N (N (N (L 0x10000000182942deefb46f6accc2fad) (N (L 0xffffffff2ec66f2756dea61509de8d) (L 0x1000000007005ee23a28a1a1052f0db))) (N (L 0xffffffffc4a6f745fa78db61ba25ec) (N (L 0x1000000001f1db1041cd983b168028f) (L 0xffffffffefda1440b5f343b7ee0a2a)))) (N (N (L 0x100000000084be82ec4a5693402323e) (N (L 0xfffffffffbc78595535afcb2cbcc9c) (L 0x1000000000220583b84c2995240cab7))) (N (L 0xfffffffffef05ec41c3d1a65dc2837) (N (L 0x1000000000086462f45fb43bad1c57f) (L 0xffffffffffbe3c9ec5e4e59fc23b6d)))))) (N (N (N (N (L 0x100000000001fea8ba30a661ec6bde4) (N (L 0xfffffffffff0a623d3e377893687b7) (L 0x10000000000075186791362ff79d1e1))) (N (L 0xfffffffffffc8a915726b5e8a13ca9) (N (L 0x10000000000019ee098d8214ff20b70) (L 0xffffffffffff3f3ea30423f6a24867)))) (N (N (L 0x100000000000058cfa97905c76e256a) (N (L 0xffffffffffffd76a823b86f804aa3e) (L 0x100000000000012654b768e8233bb13))) (N (L 0xfffffffffffff7ba6a98341fa85d84) (N (L 0x100000000000003b0b3f6eb608b5bd9) (L 0xfffffffffffffe5dd14dbb6390b403))))) (N (N (N (L 0x100000000000000b7b1d56f681c91bd) (N (L 0xffffffffffffffafeb307b710efb9e) (L 0x10000000000000022a692b1446416f3))) (N (L 0xfffffffffffffff11e0bbbe661534d) (N (L 0x10000000000000006587c0a9d7b5130) (L 0xfffffffffffffffd50551c69d4a8c1)))) (N (N (L 0x1000000000000000121085f9061211a) (N (L 0xffffffffffffffff875e7e5353808d) (L 0x1000000000000000031ff67167f984c))) (N (L 0xffffffffffffffffeb6b62a2dfe32e) (N (L 0x10000000000000000086a0a24ae9926) (L 0xfffffffffffffffffc9539f64fe735)))))))

private def cneg_lf_189 : FastDTree := dleaf cneg_bt_189 0xfffffffffff9518b24c48d8f1091e8 0x100000000000134b5a3010072d17c53 0x100000000000069d3fd759c13fcef6a 0xfffffffffffff82b6ae2b82e83edca 0x6ca17320c6d8f964fd7 0x6a1e515eb1f0f352e7 (M 0xfffffffffffa6775259851b5391f60 0x100000000000000ff6d3e0dfbcc74b2 0x1000000000000547bf0246471648fc3 0x10000000000000383ba29188265dbd0 0xffffffffffeec2000a6e532772620e 0x100000000000fbd0e83bc55ef230deb 0xfffffffffffa9059804fa2b5047dec 0x1000000000033aaa83bdafb7648ef22 0x548ee791f3b1e5891b (Q 0x5988b3138a51a71388b 0x17585885742b8dce419e 0x33f3ab1b109dbebd7515)) (M 0xfffffffffffc67241b971b8498c320 0xfffffffffffeb894d61958ae97eb25 0x10000000000002f3613640c83d5ba34 0x10000000000000d4dbec1562c0850cc 0xfffffffffff1aeccc7d3c49239e375 0x1000000000005b53b82e59325f09019 0xfffffffffff04e50f8cb63159770bb 0x100000000001d9e6ddc8039df5caf6a 0x310d12978750943f0e (Q 0x3d1562396577d1c9307 0xf69beaa66136afcc54b 0x218516036050b6d4034c)) (M 0xfffffffffffdef8d0bb270f5e736fb 0xfffffffffffe61b9e515dde43a0e4f 0x100000000000012fa873d0c4c51afc1 0x10000000000000bd26ffdb6c09e5ce6 0xfffffffffff5d08df131f5dd6dd422 0x10000000000005b83f64256211587b9 0xffffffffffefa830f66d91ca3fbf11 0x100000000000e510c665a5dd7fe951d 0x165c621b390c39015f (Q 0x29f7a6f1a83ec275681 0xa310d5305ce7072ad2f 0x15ba172c461852a86481)) (M 0xfffffffffffef7abc3476c8c93ef10 0xfffffffffffe8181c8d7f9c7b5dae5 0xffffffffffffffb1bf4f9691ae288e 0x100000000000004b8477f62f95548af 0xfffffffffff98b31583b312deee529 0xfffffffffffe09b75016d0962f0f47 0xfffffffffff2d3bd2ddbcadc37a648 0x10000000000051fe91673329f923dec 0x4bb1385e14fa7eedb (Q 0x1d0f16ae81343a56683 0x6bf71d733c5fae113be 0xe22761c579e0ee22ea2))

private def cneg_bt_191 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xffffffffef49269b35a7ccf91a9b26) (L 0x100000000902ee3369b6140d2e9d1f1))) (N (L 0xfffffffcaa8d75ffd3369c502aa1f6) (N (L 0x10000000f3298b2492b5445f7438c66) (L 0xffffffc7321c50b127413f9a83e5a7)))) (N (N (L 0x1000000b5095e54937301f5f4cdbe00) (N (L 0xfffffe06b219c0bd26ce7f4a53be57) (L 0x1000004eb63a6130aa8840987d6a3b1))) (N (L 0xfffff4e3d5945b5e4d4474f813a8dd) (N (L 0x1000016ff42e5b90a0085ffe8d7eff2) (L 0xffffd3f7649fe28a42d55404eae285))))) (N (N (N (L 0x100004e948c43cbbb5ddc46d6f96a98) (N (L 0xffff7c7bcd72627183dc19097f60d4) (L 0x10000cf87b26df0230e2ef4397ac09f))) (N (L 0xfffec9d7c1f899b52b1980f4aae551) (N (L 0x10001b8bd124a68bbf345692ebdbf79) (L 0xfffdaa77ffc830b353df74ce8382d1)))) (N (N (L 0x100030737fca7c5f6be0fe0cda952f8) (N (L 0xfffc3b003710f66b6e433747761612) (L 0x10004834f7cec0628bc906f4336e097))) (N (L 0xfffacae5d5c08aa1437c6881f24b3b) (N (L 0x10005cd6fc249bec623f69fee034f10) (L 0xfff9bedfe41b7024a63f0232966902)))))) (N (N (N (N (L 0x10006881b2b6349d097cc1b5ade62af) (N (L 0xfff961acae95073497f790a94211f1) (L 0x1000684035f1b30e15fcdcf43446982))) (N (L 0xfff9c2a5adca6d3d628cbd561f8504) (N (L 0x10005d1aaca9432575426a3f9751620) (L 0xfffab5b1dcc72759b13789e668e2db)))) (N (N (L 0x10004b170b2b54905da267a02bbc73b) (N (L 0xfffbef08e0be828056aac57544dfd7) (L 0x10003719f5f4006462097f23cb54f54))) (N (L 0xfffd2590aa7a6b627590e96e461da3) (N (L 0x100025073087b24267abbe2f027801f) (L 0xfffe293fe6f7549f49695262bbebfb))))) (N (N (N (L 0x100016eacb3226e24772bc02ecc4f65) (N (L 0xfffee7da516acc01c5d871fd8c7777) (L 0x10000d210ff501d2f89e4c5d353077d))) (N (L 0xffff655286219f7c29941047149190) (N (L 0x100006fe5e1c1efdec1cb563a888c8d) (L 0xffffb06df4746af5effe7b6dec9c85)))) (N (N (L 0x1000037a4d5affe3c55539b6f078786) (N (L 0xffffd9b77bd39c42ebb83ae0eba88f) (L 0x1000019eca1f719547105e99dc56bf8))) (N (L 0xffffeeb6ddc771e7823202e0ff9ed9) (N (L 0x100000b5a5bdafba41deaeb3b4f8ea4) (L 0xfffff8a7114c07f68fb239268405a5))))))) (N (N (N (N (N (L 0x1000004afe89a464bb929be47bb633f) (N (L 0xfffffd0d39a070f5142203e3ab5056) (L 0x1000001d44b25c5f652c394a718d070))) (N (L 0xfffffee154927bd7abc3e525569f64) (N (L 0x1000000ad31c750077983fdfd483111) (L 0xffffff98b379daa8b9e6a03f3414e0)))) (N (N (L 0x10000003cd6d309bb54068053ea883f) (N (L 0xffffffdc9b9837d36181c32cf445c5) (L 0x10000001457586c3f534a61e96ac654))) (N (L 0xfffffff47272522116594fc8e374a8) (N (L 0x1000000067c55abd98f0c3b96481090) (L 0xfffffffc667ccd3466d271776f71d0))))) (N (N (N (L 0x100000001f9c1bbe008a4be6504861a) (N (L 0xfffffffeed75ad2147d42392933a25) (L 0x100000000936d9dfc166cd87964a2a7))) (N (L 0xffffffffb1aa9ac398f3ec37518f1c) (N (L 0x100000000293090735907d4e7cc24f0) (L 0xffffffffea8febf29114001491f4a9)))) (N (N (L 0x1000000000b0bbb062fd8ed34acb24f) (N (L 0xfffffffffa5d5f167d941f3ae832cd) (L 0x10000000002d8da7d4c22705c238e66))) (N (L 0xfffffffffe9346dd748e05ee5e5d11) (N (L 0x10000000000b4cbe9b4f2a865af85fe) (L 0xffffffffffa734af83fe49377de397)))))) (N (N (N (N (L 0x100000000002b36643eb07243b4dee8) (N (L 0xffffffffffeb28a335c7c77e51a3d1) (L 0x1000000000009f683e9c0d093bf16f6))) (N (L 0xfffffffffffb475b6517379094d12a) (N (L 0x100000000000237d8445dcb101b940e) (L 0xfffffffffffef7780e5b4d89060c10)))) (N (N (L 0x10000000000007a34a6b3bfaee2310c) (N (L 0xffffffffffffc80216499d21f67317) (L 0x10000000000001972481a139f8764ca))) (N (L 0xfffffffffffff48720ef9758b0189c) (N (L 0x100000000000005219c912c85bd68ad) (L 0xfffffffffffffdb90373c08ca5a5a4))))) (N (N (N (L 0x10000000000000100bf0daa2ec9302c) (N (L 0xffffffffffffff8fc92e436c129faa) (L 0x10000000000000030ad85848b7662ee))) (N (L 0xffffffffffffffeb0a2dd97cd0a676) (N (L 0x10000000000000008f5a1232f26b8ab) (L 0xfffffffffffffffc32a4d54a3b9a79)))) (N (N (L 0x100000000000000019a20f57171d99e) (N (L 0xffffffffffffffff5467857ab1e296) (L 0x10000000000000000474bd49c799cb3))) (N (L 0xffffffffffffffffe294948176f3f7) (N (L 0x100000000000000000c0eafc81625af) (L 0xfffffffffffffffffb176d486f3c8a)))))))

private def cneg_lf_191 : FastDTree := dleaf cneg_bt_191 0xfffffffffff950a646868e6bd84c2d 0x100000000000125a4b0c77d37bfb237 0x100000000000062df2b7f92a7fd3d4e 0xfffffffffffffbcd96371a048ddb21 0x6c85beee160ab81c25c 0x62f63935c649c9addc (M 0xfffffffffffa683611ac1ed6b48c4a 0xfffffffffffff50fa14e6aeaebe749 0x10000000000004db69292058d853a04 0x100000000000006d5f196a8427042f1 0xffffffffffeead6e50d6a9beb44a35 0x100000000000f8cbbb2e8b6f6ffef6c 0xfffffffffffa39e8e7db9f4639dc02 0x10000000000338ac97cb27f71e50f30 0x4e03a8914d5b1bf90b (Q 0x597d4e1550a2dad50a0 0x17472a6d076105d1dbd0 0x33dd51850e68c0bd0b22)) (M 0xfffffffffffc694d70f156b91e7c57 0xfffffffffffeb21a97c5900566a8e5 0x100000000000028d7c345d05fba9f73 0x1000000000000102b186bc7578da3ae 0xfffffffffff1ab67c31a9ca6937586 0x10000000000058eb1bf5d5356169ad2 0xfffffffffff01a4fee45001899084f 0x100000000001d72c73b1c86969427ca 0x2bed8cac42a15e8410 (Q 0x3d17e6a8823e4a31971 0xf5eccf6309042aa9e58 0x21771eec357aa783e9f6)) (M 0xfffffffffffdf179636bdc7917ed45 0xfffffffffffe5f60839753f6d532bb 0x10000000000000d0193d9a9f530e42f 0x10000000000000e6a42e3f0b4b16242 0xfffffffffff5d6a720602f1d8d3220 0x10000000000003ff37479171e4eb96a 0xffffffffffef8ec5351f9d703208b0 0x100000000000e267528891391ff096d 0x136aad30309fc68ac2 (Q 0x29f6bbf2ae3115ff9ca 0xa2a2255e259fb949054 0x15b15ca94641605c4ba8)) (M 0xfffffffffffef889cefb767a6c2598 0xfffffffffffe81f8bb54dd15b2d769 0xfffffffffffffa1329399cae7e74ca 0x1000000000000072d83542ebc39cb56 0xfffffffffff9953f7dd5fbd284ba76 0xfffffffffffdf7f24a3f970db3ead3 0xfffffffffff2cc1975d62f8706b7c5 0x1000000000004fcc59299f72a2c436c 0x94f0d0a684d21d4a9 (Q 0x1d01161a6dae8a860ce 0x6bb1b1d9423e1f8c0f2 0xe1d040964434511dab1))

private def cneg_bt_193 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xffffffffef2373a23741869a4fd849) (L 0x10000000092a7c6a39fc63c94b0a98f))) (N (L 0xfffffffc95235a18eb972bef3188db) (N (L 0x10000000fb1d96a7bd900f46ea1cd9f) (L 0xffffffc4ebd788297d6962e9a74a13)))) (N (N (L 0x1000000bd917b47968359f939a74440) (N (L 0xfffffdeb696a565f75875e621884a9) (L 0x100000537cb83c649090b9d001eca90))) (N (L 0xfffff424cc21a353116d64a82e07c3) (N (L 0x1000018b0070850a769efcf7b91fab8) (L 0xffffd074e70737ec493429a3ff0b6b))))) (N (N (N (L 0x100005551f37b779a2e70074b57d809) (N (L 0xffff706bfa0459b9431adb1c3cadc7) (L 0x10000e3c5fd8de46dba8d27e547d4c7))) (N (L 0xfffea9d00f71c85da8b6e77083889e) (N (L 0x10001e8bc1c52e060865c28e1c876b7) (L 0xfffd6616a7bd29126d6ac5b5ae68de)))) (N (N (L 0x1000364291ece46cbc41d67ef032f97) (N (L 0xfffbc21edfe1b1bca919e98ce8d032) (L 0x100051a26a5c89048ce47bb02c6771a))) (N (L 0xfffa15e04aae3c3edd012cb10adaa4) (N (L 0x100069eceefdd40b7a73bc343006eb0) (L 0xfff8d5096a013e2fea4b1478fd5db0)))))) (N (N (N (N (L 0x1000784bb139c9e281f75e917dbb124) (N (L 0xfff859420e3d3ab0b35182834cd896) (L 0x1000790893b4db5a7dca1ac00982f9b))) (N (L 0xfff8b9b7d10800e84418257e4eace2) (N (L 0x10006cfeb2f1e3d14fed022dc91f5d9) (L 0xfff9c814ba2fbdf217c8850cb33745)))) (N (N (L 0x1000589ea22b29b6568a2337f437c11) (N (L 0xfffb2e99166d1545be0fba93e18d79) (L 0x1000418b214528d89cad1cbed5849be))) (N (L 0xfffc97c803afa16ec88c18fec286a6) (N (L 0x10002c62715612eed3925cde542a5d2) (L 0xfffdc997feb84539dcb9340c468adc))))) (N (N (N (L 0x10001bad43749cb60c35f60fb02939d) (N (L 0xfffeac6bc3f2a42ce8f8cca21ffb22) (L 0x10000ff8f5975ee1b993efb19a17143))) (N (L 0xffff432527435cd9440b50c2cc16c2) (N (L 0x10000891c4866cb864fe11a5ad3502c) (L 0xffff9e280ece3710ebbdeecb3bb931)))) (N (N (L 0x1000044a95a79899683b0f4cf4a15bf) (N (L 0xffffd098d46bf46091221c9c5ba75e) (L 0x100002035c33e9eae04b0b9c6e2a250))) (N (L 0xffffea73468d9b4a05d40efe9b6b22) (N (L 0x100000e337b93e20acff00febab9000) (L 0xfffff6c75b1c35835d130eeb96a553))))))) (N (N (N (N (N (L 0x1000005e6e762a1d41c640d66b0348e) (N (L 0xfffffc467dc424563e630f7d0488d1) (L 0x10000025183c7634aae56af76393704))) (N (L 0xfffffe9381d19cbd4f7a00131c4a7f) (N (L 0x1000000dcea05e7d9380bc26078058c) (L 0xffffff7bd2acb7b4716bc2b239a853)))) (N (N (L 0x10000004e1762c93e524cadf9c25872) (N (L 0xffffffd26e29cf8a78e1d097ca0aca) (L 0x10000001a4577a76946d12fd957b0c9))) (N (L 0xfffffff108863c249682c8e96787f0) (N (L 0x1000000086d7a406555e4f913b0744c) (L 0xfffffffb4ef49c83cdb5cf671d3c62))))) (N (N (N (L 0x10000000295253f2f1ee87b450754b5) (N (L 0xfffffffe980b434ac238e7dec00cd0) (L 0x100000000c1ddc91835f9647316febb))) (N (L 0xffffffff98b0d2e7929f5fe0ca51b3) (N (L 0x100000000367afe4d1ca51100c37ebc) (L 0xffffffffe3901f50fa93a94a144c34)))) (N (N (L 0x1000000000eb1b5379d5d9df39657a7) (N (L 0xfffffffff87b6afc729cffb94e54f9) (L 0x10000000003cf1963bfe6862ffd3d4b))) (N (L 0xfffffffffe16aec8f958465da7f822) (N (L 0x10000000000f33c6dd83910dabb1a7d) (L 0xffffffffff88356bd00aad376af2d1)))))) (N (N (N (N (L 0x100000000003a754a4cdce02a3e0809) (N (L 0xffffffffffe3ba82cbbee454a0f55d) (L 0x100000000000d8d399edf911ceb3e94))) (N (L 0xfffffffffff98f8ca232650797ec18) (N (L 0x1000000000003088ed5b6f3a4a6163e) (L 0xfffffffffffe9545d0ce61b89ab734)))) (N (N (L 0x1000000000000a803c95b37bab85b36) (N (L 0xffffffffffffb2d0ea8afdcbe976fa) (L 0x1000000000000232b6d732672455bc1))) (N (L 0xfffffffffffff01a54b423e0e4cfa2) (N (L 0x10000000000000721052088fd30ca7d) (L 0xfffffffffffffcd3f4cf5770e3906c))))) (N (N (N (L 0x100000000000001668a927012babb32) (N (L 0xffffffffffffff62e51072ba749ba3) (L 0x1000000000000004453101a8d159cb1))) (N (L 0xffffffffffffffe28177d709e3c433) (N (L 0x1000000000000000ca39a2463337519) (L 0xfffffffffffffffa9f76163474480d)))) (N (N (L 0x1000000000000000245747acf2d10b6) (N (L 0xffffffffffffffff0c1ec57526d39e) (L 0x10000000000000000659440b4471d86))) (N (L 0xffffffffffffffffd5fb54c6138998) (N (L 0x10000000000000000114346e22f3a62) (L 0xfffffffffffffffff8f4923d6d7335)))))))

private def cneg_lf_193 : FastDTree := dleaf cneg_bt_193 0xfffffffffff95056db1529afd2bb75 0x10000000000011790055d7bfeb335ed 0x10000000000005c7601e6070171e38f 0x10000000000000015b96afa20fcaa48 0x6c656ee7e03f6f80d02 0x5c7644827d314d702b (M 0xfffffffffffa6980c51aada93703b9 0xffffffffffffea1526ac63342ccaf9 0x1000000000000477c727d6b0ecc4d63 0x10000000000000acf899fdddf39651b 0xffffffffffee998578b5d9cd020083 0x100000000000f5cdd29fe53d34c4baf 0xfffffffffff9e48d8a5df0287f2f04 0x10000000000336aabe1d57a1e9c95e3 0x484cd02fc425915337 (Q 0x596aa76f5cece289cb7 0x173634cb4ff7ec745075 0x33c73313ee4d07a7ed48)) (M 0xfffffffffffc6bef7e6b6e9b982bd8 0xfffffffffffeac8694f2d734c91c72 0x100000000000023036c43abdb56a0bf 0x100000000000013b1db0e66aae9a175 0xfffffffffff1a86d29fcbed0b7135f 0x100000000000568a1fa1cba966154e5 0xffffffffffefe72bf5d91e86dd7992 0x100000000001d472bf4655f6641e391 0x282c778e3fa59dd817 (Q 0x3d0f1a309e966dca425 0xf53fc8c6cf2c5e70185 0x21694b65cca15dd9a289)) (M 0xfffffffffffdf3d44b0a1c61450067 0xfffffffffffe5dde8d8bf7ad4996dc 0x10000000000000791043c8e2671557c 0x100000000000011ac985c0f244b8829 0xfffffffffff5dcfadbddc536b003e9 0x100000000000024d42f5f9ab20c5ad8 0xffffffffffef75fbc3bd2718b9b518 0x100000000000dfc13f3fd5d7cf924cc 0x133a1dae7029bbb5a8 (Q 0x29e83c703cf6ab46ad1 0xa23484b56859004b7b5 0x15a8b727c81fc37a3b2a)) (M 0xfffffffffffef9d158d211ebed9ba7 0xfffffffffffe8339e97dd9bcca60c7 0xfffffffffffff4fb4b6785b514f88d 0x10000000000000a4d9626f8d38bcfb5 0xfffffffffff99f6669698f1989dbb4 0xfffffffffffde68e3e72b830ecadc6 0xfffffffffff2c4e30ba57760175cbb 0x1000000000004d9eac28ae879f42cf4 0xf161ebb2be4025609 (Q 0x1ce4f0f79cff6e4979c 0x6b6c9cf520bbccd933b 0xe179e033f696f26453b))

private def cneg_bt_195 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xffffffffeefdc0a938db403b85156c) (L 0x10000000095263749bce8bccab163a0))) (N (L 0xfffffffc7f5ba23822fadac7c6e9bb) (N (L 0x1000000103448533f2b5b1741662d68) (L 0xffffffc29299a66e9f0aa4c98204b9)))) (N (N (L 0x1000000c670bb673765ae0bccf256f3) (N (L 0xfffffdced8b6132646a5dc0ecdb60b) (L 0x1000005884ff49a4579a178a599b12c))) (N (L 0xfffff35a355886f7eafd3e81222904) (N (L 0x100001a7dc4f06ae41c2cfbd9b5c531) (L 0xffffccb091b2ad42155acab6f1ee34))))) (N (N (N (L 0x100005c9876b2f774ba83d8e3de09ba) (N (L 0xffff6354166d85ea90f606010ef61e) (L 0x10000f9de3304b7efe3b0d13861aaeb))) (N (L 0xfffe86aaca1dfdffbea908b9ad240c) (N (L 0x100021dac86578c79749ad92a8cda93) (L 0xfffd1a482a6b35226304040c4ef9b2)))) (N (N (L 0x10003cbb5d34b4559d074d91c515705) (N (L 0xfffb3ac930c9ee70bad3492f6fc87c) (L 0x10005c3d670371efb5b0185b972748b))) (N (L 0xfff94947a3d5884bc918b0b750f0de) (N (L 0x100078c8a1ff9a2bc5d6945bd47e34d) (L 0xfff7ca5225fb9584ad24ab3b82ced4)))))) (N (N (N (N (L 0x10008a62914d51313523ea95ee3af9e) (N (L 0xfff728fd26feb83d9ff31b2c55e4a9) (L 0x10008c6dd8a94783f5a47607f22b134))) (N (L 0xfff7863d4753ff995bc1f000125200) (N (L 0x10007f83ddff24c1db74e36d7c2d916) (L 0xfff8b2012f520911898818995cbae8)))) (N (N (L 0x100068848a579f80a9b92af70010e77) (N (L 0xfffa4b90d16107598301127f6c82eb) (L 0x10004de9610f4fb01d4544317acb44a))) (N (L 0xfffbef2ff568dc0b76ec64f8988c4d) (N (L 0x1000352a75dab38c745aa425c8c7015) (L 0xfffd56f972581a82ff8d5f7668e7e0))))) (N (N (N (L 0x10002166cc8e1b47f03b51a3b3afc43) (N (L 0xfffe64abf657418696451a5571880a) (L 0x1000136af443ed6df65ccc53d87c9a6))) (N (L 0xffff1994de7598346b63df10d6a0b4) (N (L 0x10000a7e1e96da67f253e940a717a3f) (L 0xffff87c64b0986449915196761594b)))) (N (N (L 0x1000054a9a109b2a119aa97714e1caf) (N (L 0xffffc55915dc376a164c6c35bca339) (L 0x1000027fd7482efb34dea918d2af8cd))) (N (L 0xffffe527896d44babc1bd255af7ef4) (N (L 0x1000011c01d839518a65786b0e1b739) (L 0xfffff46f880e0a399f2d4f10c1a80f))))))) (N (N (N (N (N (L 0x10000076d0ff5e2a964546717aa6d92) (N (L 0xfffffb4c58fe590bf52429718c1227) (L 0x1000002efa4f510441baa0884b61902))) (N (L 0xfffffe30e9cad6984a40363fcfabcf) (N (L 0x1000001199070b706d1ebdaa5f8f73b) (L 0xffffff5700c0801904e2bf48a24b93)))) (N (N (L 0x100000064285a027d3a840eb6c8f17c) (N (L 0xffffffc55f446540d01de291ba87cc) (L 0x100000021e7589c9bca0b118ef37b04))) (N (L 0xffffffeca04951082274a9e63294f0) (N (L 0x10000000af141452e4839f39bc34ced) (L 0xfffffff9e3e01cea867a59ad5ad39f))))) (N (N (N (L 0x1000000035f95f225de588a76e09304) (N (L 0xfffffffe286e8ae7abb684a172632a) (L 0x100000000feba192f849ff4c0a1c071))) (N (L 0xffffffff77dc9d642897df7ad11448) (N (L 0x1000000004800599294f6fe3304dc64) (L 0xffffffffda4f2a68bde8609dc10ffb)))) (N (N (L 0x1000000001388176d3a8e0770b567c0) (N (L 0xfffffffff5fa8d863e1e52f33326f5) (L 0x10000000005177845dceb9f97d93fa2))) (N (L 0xfffffffffd7010dd44b9f4fdb24728) (N (L 0x1000000000146f832e8d9b9655571c5) (L 0xffffffffff5e864687b7e4513c5dfe)))))) (N (N (N (N (L 0x100000000004f045c7a01e23bb0d096) (N (L 0xffffffffffd9ae6bd9bc4db9ce6ae9) (L 0x10000000000126aebf5cdf39f27de06))) (N (L 0xfffffffffff7399544093ee68f9052) (N (L 0x10000000000042517ee5a6b8a772936) (L 0xfffffffffffe0f0b1d66adac4b7eda)))) (N (N (L 0x1000000000000e6cd04412795bc8964) (N (L 0xffffffffffff95b16b15427424a33a) (L 0x10000000000003091264154fa2727c8))) (N (L 0xffffffffffffe9fd62357f230115f6) (N (L 0x100000000000009e55e8fdd87d84e39) (L 0xfffffffffffffb95dddd6ac10b1311))))) (N (N (N (L 0x100000000000001f4449c25f793bac5) (N (L 0xffffffffffffff243bca19befc140d) (L 0x1000000000000005fd179f988cccf92))) (N (L 0xffffffffffffffd688630ccd416074) (N (L 0x10000000000000011d07fb92353acf6) (L 0xfffffffffffffff866f4641fe72976)))) (N (N (L 0x1000000000000000337a3174b70d06a) (N (L 0xfffffffffffffffea5afe94264c03d) (L 0x1000000000000000090994ce868c878))) (N (L 0xffffffffffffffffc40a47e6025cb1) (N (L 0x1000000000000000018b1a7fda14b86) (L 0xfffffffffffffffff5e5fcf77c6254)))))))

private def cneg_lf_195 : FastDTree := dleaf cneg_bt_195 0xfffffffffff950b3be059007bdaabe 0x10000000000010a6145f4e61aca38c0 0x100000000000056b031bfed7eab9991 0x100000000000004edc1717125c09798 0x6c3e7acec03e3dbe52e 0x56d44c5b21e51b54d8 (M 0xfffffffffffa6b6c4fdf8961333e0d 0xffffffffffffdff9b47e3f76873a48 0x100000000000041e52344a5aeda09ae 0x10000000000000f5a663c5f476108a9 0xffffffffffee86428c5006d4018085 0x100000000000f2d71964590594a0067 0xfffffffffff9904270dc56a126883d 0x10000000000334a5255462b8cdc2841 0x43a94409b794225971 (Q 0x594efd2b6dad2ee0174 0x172574f52a5457d84548 0x33b14eade7958e965aca)) (M 0xfffffffffffc6f219f9e6a94d5769f 0xfffffffffffea7c2b89c04e9fe8459 0x10000000000001dd06b4e73bb6bb9a8 0x100000000000017cbde76a224b3966e 0xfffffffffff1a5db31aee13a183bf5 0x1000000000005430a58a026254dee17 0xffffffffffefb4e0b849065cf1c871 0x100000000001d1b9d70e78a3c3e6e4a 0x2625d6031572df2ec1 (Q 0x3cf9e75386081c68dfa 0xf494af1b40f936df98c 0x215b9ad0799844750dfb)) (M 0xfffffffffffdf6b54721c26da9e567 0xfffffffffffe5d1e2d53ede13451b5 0x100000000000002c003b5907db41dbe 0x1000000000000158343225c25ccda47 0xfffffffffff5e388568997c1f34755 0x10000000000000a24166f2eb7405758 0xffffffffffef5dd10f5dab137a6f0a 0x100000000000dd1e921f9cdc00a9380 0x15b05ba72c7110d127 (Q 0x29cbcb1e8b8b4ab0e17 0xa1c7cff92ab1aac5c53 0x15a0264df0bd6b3ca08e)) (M 0xfffffffffffefb99f1c7686d02b8b4 0xfffffffffffe852fc022f7e08c1217 0xfffffffffffff081228cce149e8963 0x10000000000000e0253ce0c0309e0d3 0xfffffffffff9a9a61930d8a09bf6e7 0xfffffffffffdd5891d7c33bac5f0e7 0xfffffffffff2be17263bf59076881c 0x1000000000004b75850db7ff2a56d6a 0x14e40a68c26a000379 (Q 0x1cbaed1a6e50ba37afc 0x6b27c20463e41613403 0xe1243d6a1b1ec5c34f3))

private def cneg_bt_197 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xffffffffeed80db03a74f9dcba5290) (L 0x10000000097aa3528f2c8c174ec001c))) (N (L 0xfffffffc69357d12a0c76a857583e3) (N (L 0x100000010b9f344f8d13a967f3ac585) (L 0xffffffc025e9c0ac7b0949273675af)))) (N (N (L 0x1000000cfa9f2d897308b08b99d8fe9) (N (L 0xfffffdb0f2f2dc89f9afbbfcf8955e) (L 0x1000005dd223b0f82d681f35e8299a7))) (N (L 0xfffff283729d66733d7c6ddca25fa8) (N (L 0x100001c6a3bb5ed08ec616ed66f95d9) (L 0xffffc8a5ffa4b9fa81dcc8561c0027))))) (N (N (N (L 0x1000064721a2739d6877ee48f28de65) (N (L 0xffff551f3700ca67473dfdc7b801bc) (L 0x1000111f8bb7a43b51c321791abf6dc))) (N (L 0xfffe601f37ca2c60b1bbb707180463) (N (L 0x1000258090c5742cad34d0eaf1a31d5) (L 0xfffcc64948770554e8b7de4faf2a79)))) (N (N (L 0x100043f04392cc5d2dc9ffdc8a455b1) (N (L 0xfffaa359f568e61f1e13fb1faf29aa) (L 0x10006829e4358752150f76f1133dafe))) (N (L 0xfff8622bc9a5f74653bac253840f9c) (N (L 0x100089a50674c4ff32799491c6cd5ff) (L 0xfff69a48e3566deca91dedc3f4e5a3)))))) (N (N (N (N (L 0x10009f18eb0208370fc9dedc67a7d28) (N (L 0xfff5cb13345b9d61585bfb7add1832) (L 0x1000a2d498001593acf6c992482fd12))) (N (L 0xfff6219a30f0162d1068f05c84214a) (N (L 0x1000951609c1386d20d80891510c196) (L 0xfff76cc92a707120d7deb6e13e7529)))) (N (N (L 0x10007b2fc6db8a0cc1322a5ca0ea602) (N (L 0xfff93fe532cfec7ca949db3e1db868) (L 0x10005c8d27a26280dd4d6b3b3118dde))) (N (L 0xfffb26d94d5381dcb4a958389c8899) (N (L 0x10003fa410ddcfd532a23ab944b1d5a) (L 0xfffccdba0094e3e5da0e6294281db4))))) (N (N (N (L 0x100028484680dd23ab0389e7ca5938c) (N (L 0xfffe0e1ce386a8ad80be4eb1a0d3d0) (L 0x10001796eab33ff24fbbf89952123f2))) (N (L 0xfffee712315bb6a8695e38865e68ba) (N (L 0x10000cd69b8d06265e70b43ec051332) (L 0xffff6c61317ea439a85ed0328d44eb)))) (N (N (L 0x1000068510cfcf0191b7ffe8118943f) (N (L 0xffffb77b939820ce45e74935d25395) (L 0x10000319cda007c6f3a35e6b525660c))) (N (L 0xffffde94f97f448b8cd1d5f9f376d5) (N (L 0x10000162b9c00ca8d65be0459d766e6) (L 0xfffff182149b5b83a7142383f2f2da))))))) (N (N (N (N (N (L 0x1000009562ac0a4ff1f1cd04e55872c) (N (L 0xfffffa11bbab5209c47e72e617f1e4) (L 0x1000003b72dd67aa171d60190eb18ac))) (N (L 0xfffffdb419c124d82c44b9776b61eb) (N (L 0x10000016696d4f2a68f7af59813fd9c) (L 0xffffff2817d5c33a0d4bd06f433eeb)))) (N (N (L 0x1000000805c04d8e0e22ed3abdf8d5e) (N (L 0xffffffb4a180d4e441e335cb9a25e4) (L 0x10000002bb818755f4fc01d0adfa9f6))) (N (L 0xffffffe6f0de374d02a5e05a2ba1df) (N (L 0x10000000e3242c55b9bcc4bd3cd2c47) (L 0xfffffff80ca61d33f4001101b7d367))))) (N (N (N (L 0x100000004671d80e8a274ccab099e33) (N (L 0xfffffffd96b47a393510d0324385c8) (L 0x1000000014e6ce816bc2f4d639bf964))) (N (L 0xffffffff4cbeb1c70b8b29e95fcd7a) (N (L 0x1000000005f148be45bc8f9682262cd) (L 0xffffffffce15aca354f47deb329609)))) (N (N (L 0x10000000019f0c37bea065d30596c26) (N (L 0xfffffffff2a7128d92f35f9c521a89) (L 0x10000000006ccff54260a89b1dd57dc))) (N (L 0xfffffffffc916f6a0ea4457dadd0ad) (N (L 0x10000000001b72aadd2d9be34eb22e9) (L 0xffffffffff2683cd84d416ddf639a8)))))) (N (N (N (N (L 0x100000000006ab7c468bd2ca252273b) (N (L 0xffffffffffcc1b46c03fdd09174ecd) (L 0x10000000000190295584ba54e99c8a3))) (N (L 0xfffffffffff40d429275bfa4a210b2) (N (L 0x1000000000005a8ac3096a686b100c6) (L 0xfffffffffffd57b65eaeaf81243b8a)))) (N (N (L 0x10000000000013cc885168276b6ffc9) (N (L 0xffffffffffff6db46188713aa19e31) (L 0x10000000000004302e09fd0fb7d3e51))) (N (L 0xffffffffffffe18d41405b149e8454) (N (L 0x10000000000000db9ab48ef816f210c) (L 0xfffffffffffff9dc83864507baf03f))))) (N (N (N (L 0x100000000000002b96c34054b1df3fc) (N (L 0xfffffffffffffeccd7ada1417bb34f) (L 0x1000000000000008642b61a5c702917))) (N (L 0xffffffffffffffc5bfdc00d05f7fb2) (N (L 0x100000000000000191662092314e90c) (L 0xfffffffffffffff54605f3160b2d05)))) (N (N (L 0x100000000000000048daf09bb1c4ad3) (N (L 0xfffffffffffffffe14a7ebf8067277) (L 0x10000000000000000cda8d3edfd574f))) (N (L 0xffffffffffffffffaa8307d1108b70) (N (L 0x10000000000000000234b1833ed3607) (L 0xfffffffffffffffff1870a4c11dec5)))))))

private def cneg_lf_197 : FastDTree := dleaf cneg_bt_197 0xfffffffffff951d04d804435f35ea4 0x1000000000000fdfee0fae1426678c7 0x100000000000051a19d95f0be15605b 0x10000000000000a3c751be037038057 0x6c0f1a6a662c5657690 0x52458cd3d3f76ffdcf (M 0xfffffffffffa6e0c4392606521e3de 0xffffffffffffd6a3cf574b1af346ad 0x10000000000003d046c48bb0941d7b7 0x1000000000000145d4a079d1eca7717 0xffffffffffee73a2a316e48c91c186 0x100000000000efe7764171d81139ae8 0xfffffffffff93d02c84aed183dcdfa 0x100000000003329bfa0558336ec17b6 0x4053bd163792cc3a45 (Q 0x5928d847d178b1328b3 0x1714e82ba422e8d876fb 0x339ba33c71cc9306c315)) (M 0xfffffffffffc72f7b0a56a991c6f50 0xfffffffffffea3b5c2d38295be6332 0x1000000000000195256439c3948620b 0x10000000000001c5fe24bc9c1a33e04 0xfffffffffff1a3b013fd25b8b0a6e2 0x10000000000051de8c6372f3b5d5b70 0xffffffffffef8369fee0371f0b8843 0x100000000001cf01d0352c44a32f188 0x260818b7d6a1e63bd1 (Q 0x3cd78eb1c009c7137c5 0xf3eb5b23f655c3a339b 0x214e0c8ba79fc9ae0eb2)) (M 0xfffffffffffdfa305cb31f2b9f6a5e 0xfffffffffffe5d066960d313ac758f 0xfffffffffffffea1fb316fd1969134 0x100000000000019d50698dcfcb1a6aa 0xfffffffffff5ea4ec03f279e8133cb 0xffffffffffffefe0e358431c188461 0xffffffffffef4641a14ae77d27c92e 0x100000000000da7f4fe15502bc3a55a 0x19de8b90be6b1a3eaf (Q 0x29a15f091fb199b9feb 0xa15be62ef55fc34bc85 0x1597a9bf5feef561d20d)) (M 0xfffffffffffefdf7ac0e63c980cc97 0xfffffffffffe87c18eb0b9194bc1ed 0xffffffffffffecb7ed827133048e5e 0x10000000000001232893081a0677770 0xfffffffffff9b3fe81ebfd8ec1fb17 0xfffffffffffdc4e0a501d1263e5c20 0xfffffffffff2b7b314119bded85be5 0x1000000000004950de05ea9b2c90139 0x1a839a8822e2b75cbd (Q 0x1c839ac43d50077317b 0x6ae307fb22114de4dac 0xe0cf54dc2611f5df3f2))

private def cneg_bt_199 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xffffffffeeb25ab73c0eb37def8fb3) (L 0x1000000009a33c04141664a93607f15))) (N (L 0xfffffffc52b0195d8c629cd3c81601) (N (L 0x10000001142e836e09c60be2f050e23) (L 0xffffffbda54cdfd56a5af4cd3f35cd)))) (N (N (L 0x1000000d94007b5dbaa1660d85fe2f3) (N (L 0xfffffd91aaaaa2d9c71b444fa476da) (L 0x100000636758d24b43ca89d748eb62a))) (N (L 0xfffff19fddeeffeb6a644b996d0144) (N (L 0x100001e774256a4011571260085f821) (L 0xffffc4508849c42a46097ac65a1fc1))))) (N (N (N (L 0x100006ce98caf3a85b390d370a567cb) (N (L 0xffff45b6ea030b74faf5e20568e38e) (L 0x100012c4130b00ca3f5e26a83ec7aec))) (N (L 0xfffe35de6f6d67c5d25f43d94f7b3c) (N (L 0x10002985793242ebf32828b2dccd1b5) (L 0xfffc6943e00db0452f8f10059e938b)))) (N (N (L 0x10004bf588ef6f932689add103e2c23) (N (L 0xfff9f9fe7a2fd8b9000319fd383a5d) (L 0x1000758fed90071fc4e05df907fb159))) (N (L 0xfff75d432e1e206e48d6ddafd49d90) (N (L 0x10009cc4613d40ed19f427bbf9af037) (L 0xfff53fe913d24e76598c3d66b9b2d3)))))) (N (N (N (N (L 0x1000b6cc7817b41e3233f3e0b94589b) (N (L 0xfff438e9fd40e276e99bd343921fc9) (L 0x1000bcaff9dbb84a3c1746f23dad18e))) (N (L 0xfff48434e6e86c964a520b9b4d43b4) (N (L 0x1000ae31c8c5d642e1d434a52ac51a3) (L 0xfff5f0ad3b7402d074a723a00aa3e7)))) (N (N (L 0x1000911852766da105905eb212a8537) (N (L 0xfff80485259a7b6878c12df65d0be5) (L 0x10006dde511908b38ab650f3f51d50f))) (N (L 0xfffa38f2c428ad9746276e9b181b75) (N (L 0x10004c20b8b5cb865f58956a46f1a33) (L 0xfffc297ec3a6046f7181c343e9ea87))))) (N (N (N (L 0x1000308bfe4716e49904658fb757b54) (N (L 0xfffda5c294addd467ffffa580b5d81) (L 0x10001ca326ee859862465c7efe9bf30))) (N (L 0xfffea9bb339ac8b3d0adeb3ce4d5a0) (N (L 0x10000fb2760f32ee0f471a027db8c75) (L 0xffff4adf78fc0641dfdafa4fd7ba9e)))) (N (N (L 0x100008070a52ffb537159b41189e347) (N (L 0xffffa667b57063116e2c36fab57414) (L 0x100003d8170f0226e56b619c43af43c))) (N (L 0xffffd66e56ab5ef9499205d8c29f1f) (N (L 0x100001bab9583da9c2e34768ba75fe3) (L 0xffffedda601a5e8ca822f4940e9fe8))))))) (N (N (N (N (N (L 0x100000bbada2cbab267a82cb134dfcf) (N (L 0xfffff8865431fc74daaefc821818f6) (L 0x1000004b2c52126168e8e39b3079853))) (N (L 0xfffffd16378b114a038e0115d4c1f3) (N (L 0x1000001c855dc38d4e6ea55f9c75278) (L 0xfffffeec5fd871bc63c522b9667c36)))) (N (N (L 0x1000000a4600259a7317b43df4e4185) (N (L 0xffffff9f2f30a1ad431ea88303d0e9) (L 0x100000038550e7aeec2b8d35466a009))) (N (L 0xffffffdf9cdb256b49c0608efef8f1) (N (L 0x10000001267453debe0fb5f007c4584) (L 0xfffffff5a98b8d629936331145ff8f))))) (N (N (N (L 0x100000005bde5bdc2236ac00e95137d) (N (L 0xfffffffcd89659242cbd9ce944241f) (L 0x100000001b6b59c3265c588e3ad6143))) (N (L 0xffffffff14294cbfc384c3ca0fc758) (N (L 0x1000000007d74b0f5795fe4457eaba9) (L 0xffffffffbdf2d024cd1e350f7d0c64)))) (N (N (L 0x100000000226ca6d4c49a0992939a39) (N (L 0xffffffffee3cad362527dc6cd62414) (L 0x10000000009137e6c25d4b7a65c8ba9))) (N (L 0xfffffffffb6833d586df783f182597) (N (L 0x100000000024d615fba5378ebced8bb) (L 0xfffffffffedb51782fea9ff9b5a250)))))) (N (N (N (N (L 0x100000000009002ca1fa5a0ab14e436) (N (L 0xffffffffffb9c7e3e424a1688c5857) (L 0x1000000000021ef1fc70f4425f0f194))) (N (L 0xffffffffffefbea77c80a7e5f79273) (N (L 0x1000000000007b82c470b80fe0c28f3) (L 0xfffffffffffc5d86e039003a875993)))) (N (N (L 0x1000000000001b26efc08eff12748d1) (N (L 0xffffffffffff36d7d6c454f075299d) (L 0x10000000000005c61db5f2b73e2103d))) (N (L 0xffffffffffffd5ea18fa876eb95a04) (N (L 0x100000000000013052e3f4c56e9608a) (L 0xfffffffffffff778a6750bd0222ea0))))) (N (N (N (L 0x100000000000003cb732acf3eaa95f0) (N (L 0xfffffffffffffe5310bf044927373e) (L 0x100000000000000bbf72bd260daa4d7))) (N (L 0xffffffffffffffae3e46ec2cd1fb47) (N (L 0x100000000000000234ca8644dcacfc4) (L 0xfffffffffffffff0de9ca86acbc59e)))) (N (N (L 0x10000000000000006705bf4be8a202e) (N (L 0xfffffffffffffffd477d0a94397030) (L 0x10000000000000001244082c02893ec))) (N (L 0xffffffffffffffff863859b9bc5737) (N (L 0x100000000000000003266064e3d81d6) (L 0xffffffffffffffffeb488acdc121c0)))))))

private def cneg_lf_199 : FastDTree := dleaf cneg_bt_199 0xfffffffffff953bbff2e19a776d8f6 0x1000000000000f24ca53800492472d2 0x10000000000004d59f6242ee2f4d2b0 0x10000000000000fe61567648d3ef7f4 0x6bd5cde4372cd5d86d9 0x4ef83611a9ddf702c7 (M 0xfffffffffffa717048fe7aa631084b 0xffffffffffffcdf75fedb1ea313012 0x100000000000038e9e62dab6891aab1 0x100000000000019bc760b9cc5082ac9 0xffffffffffee61a2d723543b47eee4 0x100000000000ecfecc56860f78de669 0xfffffffffff8eac9df7fbf163e3103 0x100000000003308f66d1bb9c62bcc7d 0x3e76a22d814472b197 (Q 0x58f71274bd3c4b72d38 0x17048ba97fba58c6da1d 0x33862fac392cadad40f5)) (M 0xfffffffffffc7781a4fde746ab0f28 0xfffffffffffea043deacebe29894b3 0x100000000000015989a294c1c0eb570 0x100000000000021522cd96fce56c320 0xfffffffffff1a1ea05434ed92dd3a6 0x1000000000004f93afa407f2f410749 0xffffffffffef52c3b18d865f23a26f 0x100000000001cc4abe989e53f7ecc33 0x27b57308c42141d027 (Q 0x3ca7a7eb695a31f2db9 0xf343a6f679f5500e327 0x21409ff64c107714da78)) (M 0xfffffffffffdfe55a94418e357193b 0xfffffffffffe5d7bb95bad5e7bab31 0xfffffffffffffb4630706d6307665c 0x10000000000001e86349766aa17df80 0xfffffffffff5f14d3c4321fd3aca02 0xffffffffffffd6082004cfe8a150b3 0xffffffffffef2f4a1d45b1775f943a 0x100000000000d7e37c6fa1317010583 0x1ee396bc832e7b078e (Q 0x2969414311d0f889b1d 0xa0f0a93aabd4d6936ae 0x158f411df2a973ca9f1b)) (M 0xffffffffffff00fab45643b79e1b74 0xfffffffffffe8ad41b986177250d95 0xffffffffffffe9aecd75bb5910ec2a 0x100000000000016c29921a075939062 0xfffffffffff9be6f85b5fbdb612941 0xfffffffffffdb492655dd567dc0cda 0xfffffffffff2b1b439967ed960d6db 0x1000000000004730b0ca66a69051601 0x1fe09d80218be90c72 (Q 0x1c3fd16180a93d4e8f3 0x6a9e5a0a25c74866209 0xe07b23140589021640f))

private def cneg_bt_201 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xffffffffee8ca7be3da86d1f24ccd6) (L 0x1000000009cc2d892a8c158260ee082))) (N (L 0xfffffffc3bcaa5ce0d32335e495f69) (N (L 0x100000011cf353f0081783e4ee5d7ec) (L 0xffffffbb1045fc1844e479084280eb)))) (N (N (L 0x1000000e335f25bb7a64a5a70747ab6) (N (L 0xfffffd70f1f8b690e316b17164dbc7) (L 0x1000006947f246ec58fa1daf7719912))) (N (L 0xfffff0aec99bb2f54f05c87baacec1) (N (L 0x1000020a6c8d299ef042180195710e0) (L 0xffffbfab3bde63f8036285763948a0))))) (N (N (N (L 0x10000760a31f34de295deeb2201e9f0) (N (L 0xffff35031dccbe8efbd521829e8197) (L 0x1000148e698d4de9242a92e2861fece))) (N (L 0xfffe0792dc82a28a15ca91083f5dc8) (N (L 0x10002df2a1a8d731533856866829eff) (L 0xfffc024d3695eb1df2be8d72a046f7)))) (N (N (L 0x100054e181a693db529ca0924fa84db) (N (L 0xfff93cb1e6cdd380f31067aead5d59) (L 0x1000849c147255fa4d1e1557bc21aa4))) (N (L 0xfff636e0abaec37f0f55ac2962e5b6) (N (L 0x1000b271295386f63cc3411b7b31418) (L 0xfff3b5888af04a6c9147731f1166b9)))))) (N (N (N (N (L 0x1000d1e7844a9c289528bc8212b867c) (N (L 0xfff26afbf02bf2e65dc36bca9746a0) (L 0x1000da83c44f33b2fa5aaf779d6236f))) (N (L 0xfff2a55146a70b2b1d818775d52b9c) (N (L 0x1000cb66e4788a182f28c24d95c5c49) (L 0xfff434b2515f35df1a7bb0a785bfc1)))) (N (N (L 0x1000aac9d439b56e5c35d4c080b094e) (N (L 0xfff6912e4768a2c6628a9e24b33977) (L 0x10008256beae699357aa2f9b2e9f2b3))) (N (L 0xfff91ea1ae5d90cdb1a19776cb9bdc) (N (L 0x10005b00c9137f7a3c44ea9ec84c92c) (L 0xfffb651bd31d4218c276e5aa0018c6))))) (N (N (N (L 0x10003a77731df9ff176711b3043bb20) (N (L 0xfffd280ae4be50d05ef0be4646ceb9) (L 0x100022bdaacb3f93a0be7de92e874a7))) (N (L 0xfffe5f4aea63cf47c4e235308b883e) (N (L 0x1000132dc967e0c3a5675a2442a24be) (L 0xffff21eb8ba19d15b96b0ca1e65642)))) (N (N (L 0x100009e0729435c8f460736bba06fbb) (N (L 0xffff9162d92171fd54a170f4d1a535) (L 0x100004c319bb49c7bfe35297692d63f))) (N (L 0xffffcc547bae251750a2aafb9e9e86) (N (L 0x1000022824e98ce4b556d2650b6d455) (L 0xffffe94afe57349e8d6b380896e525))))))) (N (N (N (N (N (L 0x100000eb9c5675c89efc539dcca43ed) (N (L 0xfffff695c2e54445dfe497fd228fc7) (L 0x1000005efc2655b6b62d589080e92d6))) (N (L 0xfffffc4ea69be9de8b1199ae053d8e) (N (L 0x100000244486dad5238391b1868cacf) (L 0xfffffea0684b62f5d1a2796774a143)))) (N (N (L 0x1000000d25581009132c513b09fe005) (N (L 0xffffff83bb33f25d2a3dc0606ba8b5) (L 0x100000048872860bb65d0772b2c4c8c))) (N (L 0xffffffd62c961ed81e8d547a28d900) (N (L 0x100000017d6ab6fd05ddd79f75b6fed) (L 0xfffffff291aa44411343631f33e32c))))) (N (N (N (L 0x1000000077b6a4e08a36b394644587a) (N (L 0xfffffffbe0c0a85cc13bd9ec1f365c) (L 0x1000000023f0e0ba279fd4a93996aa9))) (N (L 0xfffffffec9f6d19d4366e05c84cb5a) (N (L 0x100000000a5672dff9b3a1e3fb0ceaf) (L 0xffffffffa8aa899d4980d37484050b)))) (N (N (L 0x1000000002da57066eb1b8ae8ef0e75) (N (L 0xffffffffe86136b5e6f1684a3a6ee0) (L 0x1000000000c1a5d5520974782755466))) (N (L 0xfffffffff9dbb102633e095053063c) (N (L 0x100000000031653f2c01057e1949bbd) (L 0xfffffffffe7671c5885a6e07624479)))))) (N (N (N (N (L 0x10000000000c22d38d8b2d3b7ffc0c5) (N (L 0xffffffffffa10fce985984c2ed97d6) (L 0x100000000002e0117e6911bf8f90ec4))) (N (L 0xffffffffffe9e7455ff7879e8e1990) (N (L 0x100000000000a85833bc5ed663f7202) (L 0xfffffffffffb086424164df2eb1559)))) (N (N (L 0x10000000000025347e61bd77f1b07a0) (N (L 0xfffffffffffeeba3c0b2089f5a52b9) (L 0x10000000000007f408cd4233aa9dd60))) (N (L 0xffffffffffffc5e0d258988a4860ab) (N (L 0x10000000000001a55f078ea47d01853) (L 0xfffffffffffff4291e0b9415e02d23))))) (N (N (N (L 0x10000000000000548003687610276d9) (N (L 0xfffffffffffffda98425e5f8004a9b) (L 0x10000000000000106edce7c577ebc20))) (N (L 0xffffffffffffff8d596a5d879ec948) (N (L 0x10000000000000031a03bcbe8381e13) (L 0xffffffffffffffeaacff144d307ea7)))) (N (N (L 0x1000000000000000918e5d6071b1a7e) (N (L 0xfffffffffffffffc257fac9d26d577) (L 0x100000000000000019ef252f17fcb9e))) (N (L 0xffffffffffffffff52abde00f070a2) (N (L 0x1000000000000000047e80a23cb883e) (L 0xffffffffffffffffe25ef2cf22ace8)))))))

private def cneg_lf_201 : FastDTree := dleaf cneg_bt_201 0xfffffffffff956820da50312063c42 0x1000000000000e72c65b20a1b709469 0x100000000000049e47099801294ea6e 0x100000000000015cd09447857dd363b 0x6b91641d5cbc0f24888 0x4d0ae0ba0b6472eda9 (M 0xfffffffffffa75a3ce25997519f42d 0xffffffffffffc5d65680d88de8565f 0x100000000000035a0b18368e4fc6796 0x10000000000001f5a54f6c1183ae0f9 0xffffffffffee50403bf36645158603 0x100000000000ea1cfb9697fb2fbf467 0xfffffffffff8999325464b704c00e9 0x1000000000032e7f947f2f9da218e26 0x3e1f242deffecbaa19 (Q 0x58b8d9df252846b6d70 0x16f45cb07cd3c9a770a8 0x3370f2ed309fb04196fd)) (M 0xfffffffffffc7ccb36ab4b8cd173b3 0xfffffffffffe9d4f44b5039b9efde5 0x100000000000012ae32aa52d6aabe44 0x1000000000000268535269f88440669 0xfffffffffff1a0872ba1a9013d979c 0x1000000000004d4fe7f76262533138b 0xffffffffffef22e9d519ce4042bb09 0x100000000001c994b4db9c588f2a5a3 0x2acfef1e0b4f77765d (Q 0x3c6a21098ff305fee21 0xf29d6ec191e3192b63b 0x2133546f6a4e36707fd1)) (M 0xfffffffffffe03311316388b27d705 0xfffffffffffe5e60a7b743ba8da461 0xfffffffffffff8b77e53f6b0091e22 0x10000000000002379566aada75834f1 0xfffffffffff5f882d8e5897ec87c9c 0xffffffffffffbc972da913cc103f4d 0xffffffffffef18e73fe5e9f8ba4842 0x100000000000d54b1af2ed2e8d8273b 0x24370f4e633b2f6cd6 (Q 0x292409c3f814e30262d 0xa085fe8c4dc556c2cfe 0x1586ec0a89cebd7c7434)) (M 0xffffffffffff04af03061f0b4eefbb 0xfffffffffffe8e4a45030838dc7b30 0xffffffffffffe7707f059ca0f58b7d 0x10000000000001b95244db0ac91886f 0xfffffffffff9c8f8ec096ef170ce6a 0xfffffffffffda49bc8851d529bea17 0xfffffffffff2ac180fbe14177f402e 0x1000000000004514f6a929dd4b3368b 0x24ef1c1f980525637c (Q 0x1bf0abea877e5a08289 0x6a59a80247536ad6d64 0xe027a49031ab37e9fc1))

private def cneg_bt_203 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xffffffffee66f4c53f4226c05a09fa) (L 0x1000000009f577e1d28d9ea2cf7245a))) (N (L 0xfffffffc248451194a9befd0841f6d) (N (L 0x1000000125ee8923498152ad4394f0d) (L 0xffffffb86655f85676579f4be57e2e)))) (N (N (L 0x1000000ed8ebdb79e807ddea28d998d) (N (L 0xfffffd4eba8712341d2d9dfca11129) (L 0x1000006f7764e9643ca107cbbcaecb0))) (N (L 0xffffefaf7ff45dd79c391b4c08d302) (N (L 0x1000022fad9539a4be0d83388a11373) (L 0xffffbab0dfaaf6384053208df83922))))) (N (N (N (L 0x100007fe02d2f487559484849b1240c) (N (L 0xffff22ea056032bdf55bda9322b133) (L 0x10001681ba5c47df2b9aff99b52762f))) (N (L 0xfffdd4dfb95ca1b3218682d9e6e3a8) (N (L 0x100032d1fc28c3a0e835f0b4d9a25d8) (L 0xfffb90641d55b8bf4d12a861da06b7)))) (N (N (L 0x10005eccc53806c01fa5c590600c3df) (N (L 0xfff869382631b88d9ad863d9138465) (L 0x1000957fec0cadbdc76eb3ad514c6db))) (N (L 0xfff4eae84d87bfa58fbce157b39d4d) (N (L 0x1000cafeff72da24c709f67f85d6d80) (L 0xfff1f4c30fd6b5d529a77a897050c1)))))) (N (N (N (N (L 0x1000f0e28b2d142f4efa052c1eb845f) (N (L 0xfff058b8a6dc0c32b806698ab2f8b5) (L 0x1000fce6aa3b8cfb11ae1006d23b2f3))) (N (L 0xfff07ae6e14f50269d943d4243ab8f) (N (L 0x1000ed5b39c3b5ab3021ea51f90bd4d) (L 0xfff22e7128bae251a2f1796c23311b)))) (N (N (L 0x1000c8e6bf1c7487f588aac455f4956) (N (L 0xfff4dc3af6989531680efb39b2f6d2) (L 0x10009a855f7d39ca9f2728375822375))) (N (L 0xfff7cfd40abae769b945c1ff26fc72) (N (L 0x10006cb6290b9179b9e43e395de9180) (L 0xfffa7a6e215a5dc3309e59031169ef))))) (N (N (N (L 0x1000465d6eb172e1a8a4d6472ce29d7) (N (L 0xfffc90b0b8eecf31ad239bdc50b922) (L 0x10002a1daeb5be644ad284c177c34b6))) (N (L 0xfffe05056c24907f2cd9c211cdf6db) (N (L 0x1000176a91a2ea96fa4b4147ae7fbd3) (L 0xfffeefe6e44cb7b635e8a3dc5e1f36)))) (N (N (L 0x10000c24ad99c34b493dbc822e33bbf) (N (L 0xffff7788e4208309faedd74b070069) (L 0x100005e522ca566ad814b3e1a232370))) (N (L 0xffffbfd24e8a3b14d51834c4690938) (N (L 0x100002b019e7c9850e64abe9884c4a7) (L 0xffffe39ba57cdeffc6e8d6ec2e50c4))))))) (N (N (N (N (N (L 0x10000127909a00f903bd05b85c680cd) (N (L 0xfffff4269ce39ed3fe1277da11d3cc) (L 0x10000077ed8e5686952043ef563ec4f))) (N (L 0xfffffb5296734a7f524e48ce580f24) (N (L 0x1000002e1560ed96d596781f34ee3d5) (L 0xfffffe3fd84506b2b087ae9c9d665b)))) (N (N (L 0x10000010cefcd78ea4fdde7f59b7908) (N (L 0xffffff609dcb3e44f5dcedbc0a4887) (L 0x10000005d4ecb069b3d3d780aeb64e4))) (N (L 0xffffffca06e2b6645656a63bec0cd8) (N (L 0x10000001edad55704f34193421fda3a) (L 0xffffffee905550e6e54828a1132e75))))) (N (N (N (L 0x100000009be01710ddebdcabb27500e) (N (L 0xfffffffa9deedebd9fc0f1402691a4) (L 0x100000002f12d8ffaf6afd6cefd6f11))) (N (L 0xfffffffe68bf6596e64748a3ae66ff) (N (L 0x100000000d9e56f295057289a63abee) (L 0xffffffff8c9e7047e962c219e88ba7)))) (N (N (L 0x1000000003c7a451ffa2b8f3ab7b842) (N (L 0xffffffffe09dc916c3eae4ac902be6) (L 0x10000000010204fa154668c1a43da81))) (N (L 0xfffffffff7cb2ba4c0da4df0b332e4) (N (L 0x1000000000422ed1c8731b2d548ae36) (L 0xfffffffffdef3c5595c40658950acf)))))) (N (N (N (N (L 0x10000000001059a73650a980c4daa49) (N (L 0xffffffffff7fbf057a6fd40c45a3d6) (L 0x100000000003e5103fdd5dc9f4a18b7))) (N (L 0xffffffffffe1fcdd18d90419f8d8b5) (N (L 0x100000000000e5434b66c00c830baa9) (L 0xfffffffffff937a0a4119f860c45a4)))) (N (N (L 0x10000000000032f00c724a9e5fc2078) (N (L 0xfffffffffffe84a334e998859207d9) (L 0x1000000000000af232513db897b95a5))) (N (L 0xffffffffffffafcc7d81ac3ec88578) (N (L 0x1000000000000246f265039922dd90a) (L 0xffffffffffffef94216fa38c97fc61))))) (N (N (N (L 0x100000000000007580a1ae7086cb3f1) (N (L 0xfffffffffffffcbda7593d7fa66cea) (L 0x1000000000000016f7a287d0470aef7))) (N (L 0xffffffffffffff5f5b76a5012366d4) (N (L 0x10000000000000045b51ce15be74197) (L 0xffffffffffffffe1f8da783811d936)))) (N (N (L 0x1000000000000000cd797074e372edc) (N (L 0xfffffffffffffffa8bf83bd423143d) (L 0x100000000000000024ca55125ef87be))) (N (L 0xffffffffffffffff0983b06c04318d) (N (L 0x10000000000000000668126cb40aca1) (L 0xffffffffffffffffd5a928437a009a)))))))

private def cneg_lf_203 : FastDTree := dleaf cneg_bt_203 0xfffffffffff95a293fbaf9c8c1519d 0x1000000000000dc7ea675ffacfe5790 0x100000000000047479785b385a32ffc 0x10000000000001bd290e06b05b204f6 0x6b40ff0eb89bce34123 0x4c84ba352543849e8a (M 0xfffffffffffa7aadce128dd7e377a8 0xffffffffffffbe21571a05df2d9727 0x1000000000000332f48075174acab34 0x100000000000025182dc7b4319761c4 0xffffffffffee3f77d68c68793947bc 0x100000000000e741e150247dfbd8201 0xfffffffffff8495a2694187f253391 0x1000000000032c6caa0f313997f19ca 0x3f36da14241532323a (Q 0x586db32693e87e6383b 0x16e45896123883c30540 0x335bebf2bd6f1c4e32f8)) (M 0xfffffffffffc82dbaefe44a37b470f 0xfffffffffffe9ab8e62827e29b1e14 0x100000000000010997bfdef19f05ed9 0x10000000000002bda546bf2cefde640 0xfffffffffff19f85978e0177d2d874 0x1000000000004b130bc17fb2b5a8593 0xffffffffffeef3d8897d78eddd80f9 0x100000000001c6dfc47759a55f083bc 0x2ee40367cde370247d (Q 0x3c1f3c947fac9bae37f 0xf1f8917f811d656b496 0x21262956a46e7a91822c)) (M 0xfffffffffffe08ca12d563b20ab4c9 0xfffffffffffe5f967be54e18be132e 0xfffffffffffff6fc276bbf7f885cc6 0x1000000000000288fdd1b32141f446f 0xfffffffffff5ffee88787f9d6c7b7f 0xffffffffffffa38b4cb08ccf72c96b 0xffffffffffef0315dd17014ecc9ae5 0x100000000000d2b62dde9021d12ef7b 0x298d88a46103472074 (Q 0x28d29b7b50021cae29f 0xa01bcfabb9640a26bed 0x157eaa25d0a1be48e35b)) (M 0xffffffffffff091c26c6ed0235c5b8 0xfffffffffffe9205aa0c21290c2ebb 0xffffffffffffe6032d736991a813df 0x1000000000000208bb857efa220afd4 0xfffffffffff9d39a5b131a40efd5b2 0xfffffffffffd94fa19c6e584c1975d 0xfffffffffff2a6dc22a4b8074518c1 0x10000000000042fda88eb1c406aa0d5 0x29a6524aa7803b45c3 (Q 0x1b9784ca53e3890ed93 0x6a14e693eedc6eaf895 0xdfd4d5d0f5e48eea929))

private def cneg_sub_21 : FastDTree := (dsplit (dsplit (dsplit cneg_lf_189 cneg_lf_191) (dsplit cneg_lf_193 cneg_lf_195)) (dsplit (dsplit cneg_lf_197 cneg_lf_199) (dsplit cneg_lf_201 cneg_lf_203)))

private def cneg_bt_206 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xffffffffee4141cc40dbe0618f471d) (L 0x100000000a1f1b0e0c1b000a8194aae))) (N (L 0xfffffffc0cdc49f46c0593d60314c0) (N (L 0x100000012f210842b1ab4fbab96fe26) (L 0xffffffb5a6fb9d9a1310f4d79f883a)))) (N (N (L 0x1000000f84d8796a2b037d49dfe12ae) (N (L 0xfffffd2af58b989eca3b0c39b7c4b5) (L 0x10000075f947e3bd73e11f38ccd68fb))) (N (L 0xffffeea142fcc595648c98aee44b32) (N (L 0x1000025759960401e695d2c57d20044) (L 0xffffb55bea12d1f753f22e56f2bda9))))) (N (N (N (L 0x100008a786c85eb6e38378df20bc188) (N (L 0xffff0f4ffb5fa604c4d755ff7439e3) (L 0x100018a16f86f2d2edbe4ce34e0f2bf))) (N (L 0xfffd9d607fdbf0eaf91f1f77db4058) (N (L 0x1000382e5e4d3726b19fd981ddc714f) (L 0xfffb126eee262f6e9cea735f3a6b8c)))) (N (N (L 0x100069d26586108df0ffc08c1d53885) (N (L 0xfff77d1851d2311f8de45db14384d2) (L 0x1000a872920016ad0a6ec1d51734a63))) (N (L 0xfff374c2e502d2fa9dbfc02a02d261) (N (L 0x1000e6cbc18f86ea429d17583f82fb6) (L 0xffeff663877ace21a88e9284689cf9)))))) (N (N (N (N (L 0x1001144608ecb2bda89202727fcc0c3) (N (L 0xffedf8616006d5c38a70c0aeb63a89) (L 0x10012484e90776aac337a5c48d5f999))) (N (L 0xffedf9715fe0f0d85338a24c3772bf) (N (L 0x100114cdfee6b291f85d3fbe398006e) (L 0xffefd1de82880772385b475d749935)))) (N (N (L 0x1000ec2bec4eec86ab7564b644c6f43) (N (L 0xfff2da6876f275229315c29f299ac5) (L 0x1000b711b80664906c04128c835aac5))) (N (L 0xfff6430ad916ddac7f04fce82c40a8) (N (L 0x100081c7663d178147d40122d4642cd) (L 0xfff9622e95019482e666ac71b9a645))))) (N (N (N (L 0x100054a07ee4a7ffa5497067a303a14) (N (L 0xfffbda99da0b8a775809f1f8585810) (L 0x100033056e71d8507529bf76c408aa6))) (N (L 0xfffd97a01c372c69008648af4ff2e5) (N (L 0x10001c91def2e0761bd1be11f3ba514) (L 0xfffeb2dad5f1f44b64da79144c1fc0)))) (N (N (L 0x10000eeb54afe17470d98d70f9fdbb1) (N (L 0xffff57c33f4e67e94de3bf2ecbac27) (L 0x1000074ad25ed99ef65cf7f6d9be990))) (N (L 0xffffb057ca042f5de74cff77bab6d6) (N (L 0x10000358e854343f72e3a8de02f8ca4) (L 0xffffdc86a1af3b98f35d96df0ea475))))))) (N (N (N (N (N (L 0x100001728020a8ae328a55c0745ffe8) (N (L 0xfffff119326b7996cc22387016e8b0) (L 0x100000974ec00a271c793646fe94800))) (N (L 0xfffffa1474f061e7880413c59500aa) (N (L 0x1000003a82ffc77e68ad3c06f01955e) (L 0xfffffdc532243fff8888bf50753b07)))) (N (N (L 0x1000001579ad23eb3d350bc2240fe05) (N (L 0xffffff33bc58f9dfbe4d2e10ceff07) (L 0x100000077f2e217321f524099649433))) (N (L 0xffffffba67d65e029445bdfd61be99) (N (L 0x100000027e7b6867ff818d6455959db) (L 0xffffffe961c25a8800464c6df23601))))) (N (N (N (L 0x10000000cacd44edfc077c126b36645) (N (L 0xfffffff8f9c56f602c73eb5b2f375a) (L 0x100000003d9b25a5e04753ab2fde54e))) (N (L 0xfffffffde9788af196084d8b9826e2) (N (L 0x1000000011ed22682e36ee6b370f60a) (L 0xffffffff67af8ec9edfc4108551231)))) (N (N (L 0x10000000050105c1623489493e52ef8) (N (L 0xffffffffd655b4a42330135536c494) (L 0x10000000015783327fc6ace2994aa69))) (N (L 0xfffffffff50b4202371c7cff3f8436) (N (L 0x1000000000589a8f57e3ba8289809e0) (L 0xfffffffffd3a270050bf1a27c56c47)))))) (N (N (N (N (L 0x100000000016028003a3e2508902fb7) (N (L 0xffffffffff52e1959d90cd4045a6c8) (L 0x100000000005457ec2d599a33716eb8))) (N (L 0xffffffffffd7451d8bbab93994a115) (N (L 0x10000000000137f7da9828de643dae5) (L 0xfffffffffff6bef4a5a91c30bcff8f)))) (N (N (L 0x10000000000045ae6cd3a1970301648) (N (L 0xfffffffffffdf7ad9a170b2ce78c56) (L 0x1000000000000f0d74584bb82732a41))) (N (L 0xffffffffffff916c97fcab0f2353e7) (N (L 0x1000000000000325cdd604745edc71d) (L 0xffffffffffffe93e136f4b5050463e))))) (N (N (N (L 0x10000000000000a341c6e035d6a76af) (N (L 0xfffffffffffffb75d16ebcc239d872) (L 0x1000000000000020129bd2c47cb66ef))) (N (L 0xffffffffffffff1f1b2f541e6473af) (N (L 0x10000000000000061d5070c014d2210) (L 0xffffffffffffffd5c079f782770b3b)))) (N (N (L 0x100000000000000121cf969abb14ff7) (N (L 0xfffffffffffffff84a1e4779f3e2c5) (L 0x1000000000000000342579662863775))) (N (L 0xfffffffffffffffea1c7d02a98d29e) (N (L 0x1000000000000000091ff556ea68229) (L 0xffffffffffffffffc38ce6d9893054)))))))

private def cneg_lf_206 : FastDTree := dleaf cneg_bt_206 0xfffffffffff95eb3ca8d807c4cc55e 0x1000000000000d2234e4f748199c8c6 0x10000000000004585370d0e6ed19548 0x100000000000021d77c5fad540fa3d9 0x6ae41647820a70e00a7 0x4d52316f27d4ef207e (M 0xfffffffffffa8090b34892e350689d 0xffffffffffffb6b86aafd8ef2fdda6 0x1000000000000319769133120965af7 0x10000000000002ad6d9e2148a861362 0xffffffffffee2f46971846656b8fac 0x100000000000e46d58bf78c4b2c4243 0xfffffffffff7fa1a8cdf3cc6b11347 0x1000000000032a56ccd6cc6b73c5bc6 0x4188aee98af5991702 (Z (Q 0x4feecdec838fc712e66 0x149296671615c4ed4a8d 0x334719b3f8719c05ffc9) (Q 0x610e3aaa7fe9d697319 0x194afb2cb6e3fd394c33 0x334719b3f8719c05ffc9))) (M 0xfffffffffffc89b5c9c9f0e0aa6287 0xfffffffffffe98611cf6892faee5be 0x10000000000000f5c1fcdeee86e6191 0x100000000000031327ae268fc255c81 0xfffffffffff19ee33dd7b3f8516560 0x10000000000048dcefabdfd8538f67e 0xffffffffffeec58c0855ebd71d0eb0 0x100000000001c42bfdcd71191dc455c 0x338a58d17926cde1f3 (Q 0x3bc78e7186aaf1cabbc 0xf154f18f913bed3ca50 0x21191e0cd3e06a9efcfa)) (M 0xfffffffffffe0f2397868f0e7f1d91 0xfffffffffffe60fde9447baf7fa238 0xfffffffffffff615c3526d143851fa 0x10000000000002daad4fd18c36266a7 0xfffffffffff6078f1bb27280f61a4c 0xffffffffffff8ae1a55196fbc61e77 0xffffffffffeeedd2deb22a3f60651a 0x100000000000d024b6fe5e57ec8f618 0x2ebb7fcf17ce5f0c81 (Q 0x28761f96c9f4d8abeae 0x9fb20a9105cd8740802 0x15767b10fe3f6e4fb17e)) (M 0xffffffffffff0e4529208e7a60e6d5 0xfffffffffffe95e758a026b2ec6ee1 0xffffffffffffe5686074d4e6b50210 0x100000000000025878231d04f668c72 0xfffffffffff9de535268b2304b49f4 0xfffffffffffd85aa8e312ab4dfbd0c 0xfffffffffff2a1fe1050b72b58856e 0x10000000000040eabf10338cf68875b 0x2dff3c31f080fd9bdd (Q 0x1b35f120710e032a9c1 0x69d00f6aa8e893e4a7f 0xdf82b364b27ac27693c))

private def cneg_bt_208 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xffffffffee1b8ed342759a02c48440) (L 0x100000000a49170dd73439b97755377))) (N (L 0xfffffffbf4d1bf1498d4e11a50fea9) (N (L 0x10000001388bb876466be8cb8d1c89a) (L 0xffffffb2d1b3968becf5965b8d96fa)))) (N (N (L 0x1000001037580f4ff794e0aa018ea48) (N (L 0xfffffd0593c547a5c616beb1892399) (L 0x1000007cd155c4585a0986526074a1c))) (N (L 0xffffed834c19797208d3ef74028814) (N (L 0x1000028194b1aec11e44973ce7bcc96) (L 0xffffafa67e756709f057e246ca7d72))))) (N (N (N (L 0x1000095e0b4ec3eee1ef63cda0da50a) (N (L 0xfffefa17634d46a145564d4b6285c0) (L 0x10001af1368a7e959b3821cf2837d63))) (N (L 0xfffd60a84fe5953a16285276497c36) (N (L 0x10003e13944388aeff84fd107edeb17) (L 0xfffa87395d198c7f3608746ffb65b2)))) (N (N (L 0x100076102b0452a4036a770cb5e515e) (N (L 0xfff67596950d59a8dcbed3b21fac1b) (L 0x1000bdb144c28b7323100bfd9a100ad))) (N (L 0xfff1cf504d2b3674be5527a0f180b3) (N (L 0x10010640bd1830cac12f6a28c538321) (L 0xffedb24a72129d3067ce8d12f6e6da)))))) (N (N (N (N (L 0x10013cac83fde1b2d2ff0ae4eeb71eb) (N (L 0xffeb3ee0f02a3c4c36fb656b6e27c3) (L 0x100152233f483b5c6fa76f95f0f9720))) (N (L 0xffeb13ba56af7d3ab6d5ac4bf0e7ab) (N (L 0x1001429b810bc8b4c315df13cc48582) (L 0xffed110b1b0c53e94a466b19faff4a)))) (N (N (L 0x10011574c27ff347be5b80ef3feb841) (N (L 0xfff07e93f6f2d36f9b473c2a9d31ef) (L 0x1000d8bffc8829045acf4a03c453326))) (N (L 0xfff46d1b776edc7466c02453c8f13c) (N (L 0x10009ad358b6d8ec704d93f3d2ec361) (L 0xfff813bd33f7c44dc8f8dd49bfc464))))) (N (N (N (L 0x100065b5e27eb2eb58e3e8efae77ad7) (N (L 0xfffaffae74c5aa8432a3c45ec0ceeb) (L 0x10003dc44d98604997c7b7d7581fdc9))) (N (L 0xfffd13254484a92c08abfa45d910ec) (N (L 0x100022d54662ebd451e8bec856673f9) (L 0xfffe6866389b73808427701c9bc2a0)))) (N (N (L 0x100012511b0b0e015c0c6ba8b718cd1) (N (L 0xffff30bde7d25127086f279f38a7e8) (L 0x100009039f058554bfd4a4cf6219f08))) (N (L 0xffff9d33edf2dc12d7383938019105) (N (L 0x1000042a5911e0caeb5ab0555e8e29f) (L 0xffffd3b5b2b16389c52ad57f11ab12))))))) (N (N (N (N (N (L 0x100001d017a9e3830afad3c112e08d8) (N (L 0xffffed460a71e5e0055f1f29a08a06) (L 0x100000bec171efd5e71ea53b5db2f40))) (N (L 0xfffff8833db50039f7404d0653314d) (N (L 0x1000004a3c59b071350e1d0cc942026) (L 0xfffffd2987e7babaa5d130636a921e)))) (N (N (L 0x1000001b6ab8f19c816894f7c81f46b) (N (L 0xfffffefa6ac31bfac06d790b2935a6) (L 0x10000009a13f52d1e78af16f4aaf14e))) (N (L 0xffffffa6550c1178b601b5fe328a91) (N (L 0x10000003391f5e915cd7583c29228de) (L 0xffffffe2aec48dcd9e92aee3bc6e51))))) (N (N (N (L 0x1000000107a65fa764cd6f95ef3f0c4) (N (L 0xfffffff6d757781d9a40666973ab5a) (L 0x10000000508fc0616319561e08badcd))) (N (L 0xfffffffd42f8535bf3d50a146310f5) (N (L 0x100000001793fbdb958deb9ed187125) (L 0xffffffff371712d829adc44463b7db)))) (N (N (L 0x10000000069e8b1377d4df3e8c99bd5) (N (L 0xffffffffc8baa779bb92764f1a0b2f) (L 0x1000000001c8f75da4572e311248fd5))) (N (L 0xfffffffff162809db4e8aa2d65a6dc) (N (L 0x100000000076863f7afded17540d3ba) (L 0xfffffffffc47d36b0cbc1374e0fbdb)))))) (N (N (N (N (L 0x10000000001d9ab32aaf6bd3d0990eb) (N (L 0xffffffffff16831a60db141466ed58) (L 0x1000000000072102448b949dee57401))) (N (L 0xffffffffffc8c52129a5287a8f3b81) (N (L 0x100000000001a829093da5e7f772f55) (L 0xfffffffffff3626c4137a5a6e3d1eb)))) (N (N (L 0x1000000000005f3e521850b90deccca) (N (L 0xfffffffffffd36eef40298a37a9fc4) (L 0x10000000000014aeb2e110d37547527))) (N (L 0xffffffffffff67ac34fdbf5335d81a) (N (L 0x1000000000000458edde1498cdd833c) (L 0xffffffffffffe07ce7bfa10140c77a))))) (N (N (N (L 0x10000000000000e2a341bf021261217) (N (L 0xfffffffffffff9ae870a246907b998) (L 0x100000000000002cc00a7032b9573dd))) (N (L 0xfffffffffffffec56c3857fd1d030e) (N (L 0x1000000000000008930254996b021aa) (L 0xffffffffffffffc49bdd69c3b991da)))) (N (N (L 0x1000000000000001986a7f4790af149) (N (L 0xfffffffffffffff51b74843810e180) (L 0x100000000000000049d94f4634f7917))) (N (L 0xfffffffffffffffe0ed0b401491a2e) (N (L 0x10000000000000000cfc4328d3ac5bf) (L 0xffffffffffffffffa9c47798dfb7e8)))))))

private def cneg_lf_208 : FastDTree := dleaf cneg_bt_208 0xfffffffffff9641f4e729015753f60 0x1000000000000c7fa5967a4a51c66e2 0x1000000000000449a645bb9e9b4a6d6 0x100000000000027bce1f664840fa8f1 0x6a7a77a269a4829cd94 0x4f4847f0bbe39f71ed (M 0xfffffffffffa874a5503510e8111a0 0xffffffffffffaf7bb12a83c08c1270 0x100000000000030d62133caff5f127e 0x100000000000030777a7d152f573613 0xffffffffffee1fa9540ccea88bf540 0x100000000000e19f3ba803b69dff4b2 0xfffffffffff7abd01c976a2a6d0a75 0x100000000003283e20962d3f78f4924 0x44ce3bca8e975dfb1d (Z (Q 0x4f8ad046328c43959e4 0x1484ab057c9c346bee37 0x33327b2c0044f677dbc3) (Q 0x60a74c0597798fb77f3 0x19399d8dad69c60bfb82 0x33327b2c0044f677dbc3))) (M 0xfffffffffffc9157b33902632507b0 0xfffffffffffe96285c9b2b3e4f5d2c 0x10000000000000ef31d13d725fc1e58 0x1000000000000366ee3e3989cd377c1 0xfffffffffff19e9df32d3a9ccbfedd 0x10000000000046ad6739a7ca174220c 0xffffffffffee9800a37b7da0cc192b 0x100000000001c179703a024605930dd 0x387330366d5b13407e (Q 0x3b63f799164495e2dba 0xf0b27533f901607363e 0x210c31f4a56b3050078b)) (M 0xfffffffffffe163c04e6b4003e5da0 0xfffffffffffe6277bed3558c833a71 0xfffffffffffff60146d13f53e32fbc 0x100000000000032ab9888e129115d4d 0xfffffffffff60f633d89ecdd0f8cb7 0xffffffffffff7297508ffe9e7cd9b2 0xffffffffffeed91b433702d61b0a00 0x100000000000cd96b78486eb06768ff 0x33a5d7c70b0107db6b (Q 0x280fffec175ae3233f3 0x9f48a1e37018bf765d8 0x156e5e6e8dc3854523ef)) (M 0xffffffffffff14288d585ce80d6fd4 0xfffffffffffe99d07c125801a0ee35 0xffffffffffffe59d049d5c6982ebe5 0x10000000000002a69ffb2ba39e3b75d 0xfffffffffff9e9232731ec6b100372 0xfffffffffffd76aa4d6281d4e0355f 0xfffffffffff29d7b878fb956bb2d4b 0x1000000000003edc3276441f6ae8e08 0x31f411d7697fdec7f6 (Q 0x1acdbb245b3d8769880 0x698b21259cc06ad299b 0xdf3139f2de7dc938141))

private def cneg_bt_210 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xffffffffedf5dbda440f53a3f9c163) (L 0x100000000a736be133d94bafb0b3eb3))) (N (L 0xfffffffbdc63df2ef86f9948f89c51) (N (L 0x10000001422f82d32fc821dd6f7edda) (L 0xffffffafe5f86ae9a850fb9d458696)))) (N (N (L 0x10000010f09ee4e4db74facbdc7fefa) (N (L 0xfffffcde85795ef75a6c8d52f23aca) (L 0x10000084036d9967570be9689d75223))) (N (L 0xffffec54cbbb225fea40c98da04038) (N (L 0x100002ae84e8d027bade4efa9d80e70) (L 0xffffa98a68df7dc2ac0b54cc062d74))))) (N (N (N (L 0x10000a227aeb3c50745ca847be4a3af) (N (L 0xfffee32088fe3ef98d4c72f6e09372) (L 0x10001d750519b8d7b62ac526b3bb718))) (N (L 0xfffd1e414aefbd57a3c27ee91d13a5) (N (L 0x1000448e75383eee1e033fccc800174) (L 0xfff9ed721bbee5971fcee659152afe)))) (N (N (L 0x100083a6d640334254af5fe709ebe06) (N (L 0xfff54fad7c82d772e1f8e0c83bff6d) (L 0x1000d58009159644f49ca164108bf6a))) (N (L 0xffeff4d83a6e390d000d9676cf6f2b) (N (L 0x100129d40343b458022dbf458344e2c) (L 0xffeb1f516f7d2a6f3d669fc9735054)))))) (N (N (N (N (L 0x10016ac4d653849503749eff00face6) (N (L 0xffe81f9e9bb8e6d2361359bd14b79e) (L 0x100186a247af1b7a8416088e4cfe784))) (N (L 0xffe7ba9ba987a7ed541cf9718464bb) (N (L 0x100177c16a1706950444c481df7b20f) (L 0xffe9dbda3351389cdcbf11312265c4)))) (N (N (L 0x100145bffee004467accbb35b678e4c) (N (L 0xffedb96d119f6e64d6978023bfa48e) (L 0x10010075d53e31f4092bc4cdc2b0178))) (N (L 0xfff240e690e417dfd177f874e172b9) (N (L 0x1000b895666cfa0935fab1ed8c601e4) (L 0xfff684e3037bddd0c3cb2bfe4aa318))))) (N (N (N (L 0x10007a28fcfbae8e9e4462e0afb3f36) (N (L 0xfff9f8a91b1331ced93fd90b5a76f3) (L 0x10004ab964171a68398c3268c4f9782))) (N (L 0xfffc72d22bbcd850cd548d02f40741) (N (L 0x10002a709bc1c948561592b7789e032) (L 0xfffe0da75df8a68f5a17cc4879f15a)))) (N (N (L 0x10001678e1d788184ee596d5b97b661) (N (L 0xffff00da2f189d2145eacaa96ab50d) (L 0x10000b227589ab8710202f4f15b811e))) (N (L 0xffff858d598152ea88cbfc71895bb1) (N (L 0x1000052e040801e7fec6ffa734298e3) (L 0xffffc8be31d5e1b92cd53ae6bb4a7c))))))) (N (N (N (N (N (L 0x10000244e660f8f8cc968ccb359f1c0) (N (L 0xffffe87c02058c8614d0ab89de19eb) (L 0x100000f04f55cb33acc5d4a20140a13))) (N (L 0xfffff6899e240c66167432bdcd757f) (N (L 0x1000005e1d5fdfa491b15d4f66dbd60) (L 0xfffffc641c4f564b05742968eb3df2)))) (N (N (L 0x10000022f9d1188af20de5f5021b08b) (N (L 0xfffffeb144ceacfb43379a557aa095) (L 0x1000000c5c450bc7d8d03d4c082ae21))) (N (L 0xffffff8c8ebc9cd1dc3f59b48a4a7a) (N (L 0x100000042980154a3e21aa19bd8ff6b) (L 0xffffffda0757a1ec7c8ee22d5230cc))))) (N (N (N (L 0x10000001567d0e54147e68bded00abf) (N (L 0xfffffff4114045e9a548d974e721c6) (L 0x100000006944583fd601abe86efb37c))) (N (L 0xfffffffc6953ea39bb24985fb64451) (N (L 0x100000001efcbbe713d55d69bdcd9f5) (L 0xfffffffef73322f7b7a73efaf02274)))) (N (N (L 0x1000000008bfc57c5f6ebc8bfa7c0be) (N (L 0xffffffffb6bd2bb0aee9d48188dc87) (L 0x10000000025f67c1e37a3f09bc9b200))) (N (L 0xffffffffec84e1a6e2b7feb75993a1) (N (L 0x10000000009e6be61a40f21293080f2) (L 0xfffffffffb03ce025e936f07477a5d)))))) (N (N (N (N (L 0x100000000027c980c27b2bd62055d30) (N (L 0xfffffffffec558d7539de9f9363208) (L 0x100000000009a21159ba556c0e91f86))) (N (L 0xffffffffffb52b51e75bba539732e5) (N (L 0x100000000002403a4a17e425bb8c0e3) (L 0xffffffffffeed0ec4e38424218ce71)))) (N (N (L 0x10000000000082135f33341340fee2c) (N (L 0xfffffffffffc2f98870b672fc49fd6) (L 0x1000000000001c64f864a3acc517adf))) (N (L 0xffffffffffff2e549e2ebca43e31a5) (N (L 0x10000000000005ffd5a38a9edb23571) (L 0xffffffffffffd466e385bb34c30a4e))))) (N (N (N (L 0x100000000000013a5ca17578da32670) (N (L 0xfffffffffffff736c2603e5e994486) (L 0x100000000000003e62e41a7195fc7a2))) (N (L 0xfffffffffffffe4858641841977164) (N (L 0x100000000000000c036c584c0ba4fca) (L 0xffffffffffffffac948b137821d710)))) (N (N (L 0x10000000000000023f12b11d78fcf8d) (N (L 0xfffffffffffffff09fe7b58cdb5661) (L 0x1000000000000000687ea25d12ea397))) (N (L 0xfffffffffffffffd3ec76f7cf99cd7) (N (L 0x10000000000000001276a9bfd96f978) (L 0xffffffffffffffff8517bf868ee876)))))))

private def cneg_lf_210 : FastDTree := dleaf cneg_bt_210 0xfffffffffff96a64ee6f7da9d2af1d 0x1000000000000bde488d2c8c68ebcb4 0x1000000000000447f9fbb116449b597 0x10000000000002d64cf61ee60536add 0x6a044649dedc35bf7e3 0x522d034ee1b898d078 (M 0xfffffffffffa8ed40ee3bcd01c17b7 0xffffffffffffa84c1052e7290ef990 0x100000000000030e3ec48c1abb06020 0x100000000000035dc297275fef2af39 0xffffffffffee109cc6e2a59acac219 0x100000000000ded762f10964e8d7338 0xfffffffffff75e76b3c1aad2b2301a 0x1000000000032622c78fec2e96ddf28 0x48bde48a36c10854b0 (Z (Q 0x4f1ab7a930ff5679dd0 0x1476dd40484a5e3bce97 0x331e0f5a580540a3f36a) (Q 0x6033d5b543c2a4d7792 0x1928694b767f1189b33d 0x331e0f5a580540a3f36a))) (M 0xfffffffffffc99bb1fde4fb6895b72 0xfffffffffffe93efdfd6f73d4a1a57 0x10000000000000f56ea4ec2ca97689a 0x10000000000003b71c56907e70e5014 0xfffffffffff19eb36928f962a5aa2f 0x1000000000004484455f2f6b1a77693 0xffffffffffee6b32c3b84029899980 0x100000000001bec82a25c58b2460d7c 0x3d6493b9b522c84e65 (Q 0x3af5a0ad82aa2b94775 0xf01106f204427588a42 0x20ff647333fa74dc25e6)) (M 0xfffffffffffe1e0d4bd4cd47cf1eac 0xfffffffffffe63e593c05d6b5fa4ea 0xfffffffffffff6b7262c4a56a6f688 0x100000000000037747e9215692e436d 0xfffffffffff617697090ab9e510f1c 0xffffffffffff5aa961760d1ff98528 0xffffffffffeec4ec1ca3152e6ab371 0x100000000000cb0c30179668a8df494 0x383a6125b16e762220 (Q 0x27a1e06d2aec84169a7 0x9edf8d16970bc5bd982 0x156653e2e925c789acea)) (M 0xffffffffffff1ac0692b507d6d04fe 0xfffffffffffe9da30888f069eb50f9 0xffffffffffffe6998dc0a75e4c6607 0x10000000000002f15ac8c9fbb588018 0xfffffffffff9f40901c95fd74f8ab8 0xfffffffffffd67f67a918e552bcc78 0xfffffffffff2995246f10805367336 0x1000000000003cd1fac7c798acc95cf 0x3580102458f4ee374e (Q 0x1a60db641141690764a 0x69461f2e891b8ae4b7a 0xdee066459bde74241c2))

private def cneg_bt_212 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xffffffffedd028e145a90d452efe87) (L 0x100000000a9e1988220a35ed2db0c5b))) (N (L 0xfffffffbc391d8f8b23b7e0d84ad01) (N (L 0x100000014c0d525bb7f3952d8530838) (L 0xfffffface3427afbd0b2c31ca96fcb)))) (N (N (L 0x10000011b0e27ee63c43b4977591020) (N (L 0xfffffcb5ba707b1ed82c64a9c8d246) (L 0x1000008b9394132f002064b48268802))) (N (L 0xffffeb14e9072e89fc9247f36f036c) (N (L 0x100002de522fed3ad27b8e1ae956b8d) (L 0xffffa301198ac19a3fc89a4e0d04d0))))) (N (N (N (L 0x10000af5cf2bab4946a52c6ae5bf055) (N (L 0xfffeca497e28e144c75ff5e8135ed7) (L 0x100020311e3367db1630f9909dac262))) (N (L 0xfffcd5abe3efaed6122dbd8f19bf5b) (N (L 0x10004bacf9551e6068f2d9f7d251be1) (L 0xfff943a84a722b348c3ea424f0e5f2)))) (N (N (L 0x100092ba673448ddabba44794c86dee) (N (L 0xfff40806a4496951766909026dceeb) (L 0x1000f02a5ffb6c77a30cd2402ec674c))) (N (L 0xffeddef9714ac1a3ebb0da27458e17) (N (L 0x10015209e302de2483a2bd42fedcdd2) (L 0xffe8332b763d3e4e4f3aaaa97de7b2)))))) (N (N (N (N (L 0x10019f54bd859de4bc0dd56d42e2c5e) (N (L 0xffe48c4b3c59db776c7e4442b29189) (L 0x1001c30244ef74c9072e0299679ed06))) (N (L 0xffe3dcb985941a956afdea589410f0) (N (L 0x1001b563a15452395da8df54700c559) (L 0xffe61fad56d9a8ea41ea4e56ee0727)))) (N (N (L 0x10017e3537a30dd4abe17fd4fe73d56) (N (L 0xffea791c3470b365ca594ab16becdc) (L 0x10012f3fe7267a38fc45292f66302a0))) (N (L 0xffefaf02efa775a457d4491a32d6c7) (N (L 0x1000dbea80c1c65ab12b69cdb7e3e58) (L 0xfff4a98906f2bc1a9a9bc24d398b4a))))) (N (N (N (L 0x1000929f6939c278f74ae8b6e56a179) (N (L 0xfff8bcddecfe7a701b344bea6ba972) (L 0x10005a5685e8c81bf35b865c055f292))) (N (L 0xfffbb0ee9d10cfc3e1d185cd7cbfec) (N (L 0x100033ac02f52b8fd2e1247d7f85f8d) (L 0xfffd9f2190be195b97dc7f4960e22c)))) (N (N (L 0x10001b8d0551da19c08a5ddfb797388) (N (L 0xfffec61eaf3c19c247fea55775bbeb) (L 0x10000dbe7b32bebdf68060956679d8b))) (N (L 0xffff6859459a6999082afafc3f30c6) (N (L 0x1000066fb98c38b0dfcdbd0ffc6a32e) (L 0xffffbb1c5705486747427bf81d3b5f))))))) (N (N (N (N (N (L 0x100002d6934fff85b40562d417c7df8) (N (L 0xffffe27dfa089dbf0e556b802840d6) (L 0x1000012e838108922a75012844da683))) (N (L 0xfffff40ce385454dd0ca5e9ed3d50c) (N (L 0x100000773a5a7a06cf02c918a7232cf) (L 0xfffffb69ebfd6b9ec9e9c0885f77de)))) (N (N (L 0x1000002c95d1951e86050253d6ecebf) (N (L 0xfffffe53fd647ba1e3f715f0a5db6c) (L 0x1000000fda696b3aba5e860e9ef6adc))) (N (L 0xffffff6b7cd4031a94a067b7f46150) (N (L 0x100000055ed9bacdcbce4711a071d48) (L 0xffffffcedba7d27782ee0024c84b3d))))) (N (N (N (L 0x10000001bc8ed65ee1608efe834034b) (N (L 0xfffffff077323d1fe4b236d404ff92) (L 0x100000008971072df2e9d0a0278b8e4))) (N (L 0xfffffffb4d0edc0a709a18822331dc) (N (L 0x1000000028b1556be7f7ced107cea8e) (L 0xfffffffea344551788de44479d8929)))) (N (N (L 0x100000000b8e16aec2e2d5cb0841819) (N (L 0xffffffff9ef85e7e68c1ad6b31a541) (L 0x100000000326ba5d70c169cb22d23bb))) (N (L 0xffffffffe60de0923e2b1e184f87a7) (N (L 0x1000000000d3942e841503dcf2e815a) (L 0xfffffffff952e531ef8166d7f1c17b)))))) (N (N (N (N (L 0x1000000000356dead5c3ff9661292da) (N (L 0xfffffffffe584f6a595bc94fd90e27) (L 0x10000000000d019ad35f2bc61ae4079))) (N (L 0xffffffffff9ab1d38bf6ca7f9a8567) (N (L 0x1000000000030e2cc72a0bc6feeddb6) (L 0xffffffffffe89cd298e04b9df28ea4)))) (N (N (L 0x100000000000b180412c393e2ead6e1) (N (L 0xfffffffffffac81b2cbd2d0b2b8883) (L 0x10000000000026f32d04c6fc2808006))) (N (L 0xfffffffffffedfa41904ea71cf861c) (N (L 0x1000000000000845af5d91cb3565e6b) (L 0xffffffffffffc3bb083f3418757012))))) (N (N (N (L 0x10000000000001b3ad982886f65f2f2) (N (L 0xfffffffffffff3cad6c505ab3c3fce) (L 0x1000000000000056e66e379f4015776))) (N (L 0xfffffffffffffd9a0d310d6ada3363) (N (L 0x1000000000000010d15975fdc5a34c6) (L 0xffffffffffffff8aedc399e9635e8b)))) (N (N (L 0x1000000000000003290d62aadf5168e) (N (L 0xffffffffffffffea50cf6ec91edf79) (L 0x100000000000000093bb891b423ad21))) (N (L 0xfffffffffffffffc188b4370a7dbcf) (N (L 0x10000000000000001a3af94e2243abd) (L 0xffffffffffffffff50f83dfa502195)))))))

private def cneg_lf_212 : FastDTree := dleaf cneg_bt_212 0xfffffffffff97179813ee77f107732 0x1000000000000b3c40b34535e67b0f5 0x10000000000004529101827dc48e6b4 0x100000000000032b2f2f1157ff4979f 0x6981f8234fb65a2fe53 0x55c1146a12a9edbf77 (M 0xfffffffffffa9722f2130d08fdab35 0xffffffffffffa10bdbd8cf6c354cb2 0x100000000000031b4f0fdadb56ac4eb 0x10000000000003ae8a19f37a21540bd 0xffffffffffee021d8a58fffe7dd4a0 0x100000000000dc15a7422608bc37d3d 0xfffffffffff7120a48b699459b1984 0x1000000000032404e29ff1aa4dcaa36 0x4d144b97eaac630199 (Z (Q 0x4e9f7f755e6e2c7be96 0x14692b66637b440d2ac4 0x3309d5434df05553083b) (Q 0x5fb47cb467a9db8f932 0x19175c402c34ba16f4ae 0x3309d5434df05553083b))) (M 0xfffffffffffca2d57e0a6ae5087820 0xfffffffffffe919a4f833a6bcc59f9 0x1000000000000107bb0e2bde78c0828 0x1000000000000401ef7234787912df7 0xfffffffffff19f212ce26a8db69d61 0x10000000000042615d1971d3e426547 0xffffffffffee3f1ee79f8088cc4b8c 0x100000000001bc183917f0259e734cb 0x4234f5670a68c5bec3 (Q 0x3a7df373a7ec47f0b4c 0xef7095d3351a6f07dee 0x20f2b4f09df1716c54da)) (M 0xfffffffffffe268d1bd0ce672a3c60 0xfffffffffffe652a6d11cc20268f92 0xfffffffffffff82b9069007d0b4339 0x10000000000003be9801bb1c871bfbd 0xfffffffffff61fa00dcb2337f78947 0xffffffffffff4314ee4c202f72035a 0xffffffffffeeb1428f6829a816cd91 0x100000000000c88520e07557afe0b0c 0x3c6c3460b8f3ab7608 (Q 0x272d9786eddc1585180 0x9e76c866a0073ba4f0c 0x155e5b15035999cd58ab)) (M 0xffffffffffff2202966e0bc0d1d24b 0xfffffffffffea1425f812f0a36039d 0xffffffffffffe852322097df18bded 0x1000000000000336ea6e433fafcd03e 0xfffffffffff9ff03dcd25ce482c9e8 0xfffffffffffd598c3d92cdf487004d 0xfffffffffff295801bdcbf01477e03 0x1000000000003acc0fd4fda79e9eb59 0x389f5f364c431a8256 (Q 0x19f1708dcd886dae94f 0x69011171ac94b2eadbe 0xde903551ba234d0931b))

private def cneg_bt_214 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xffffffffedaa75e84742c6e6643baa) (L 0x100000000ac92002a1c6f871ee4bc7f))) (N (L 0xfffffffbaa5adb26ed9e51137fef6d) (N (L 0x10000001562613ff4b507338668105f) (L 0xffffffa9c907fb0bedcc7db8baedb9)))) (N (N (L 0x100000127859a42e07a80641681997c) (N (L 0xfffffc8b21f3a492b1019ca5e3a87a) (L 0x1000009385f4ad263265e6548204e1b))) (N (L 0xffffe9c2c17dc8e67a69f672fa6f7e) (N (L 0x100003112685c9348c5a7409381e75c) (L 0xffff9c03a029b1efb9d8096d088578))))) (N (N (N (L 0x10000bd911849b15682bab12d6c1892) (N (L 0xfffeaf6df5f4f402f6f2c205ff3166) (L 0x1000232a178c2153e6a40552c3a0e43))) (N (L 0xfffc865e22e9ab158a3833c8e61980) (N (L 0x1000537e516c7dd8b07bbe1c987ed4a) (L 0xfff88848b3e6a8629b1293e8f5405e)))) (N (N (L 0x1000a3726ae0ea2685d46b3fbab2bc9) (N (L 0xfff29af2b6cb963448faf41a95ae10) (L 0x10010e040eb6bafdaca21945e6ddf5f))) (N (L 0xffeb86973b56833b738f92557dcb88) (N (L 0x10017f768c88d809ccbb4b63545a96d) (L 0xffe4e2415fc2b7e6f0e75303c286fd)))))) (N (N (N (N (L 0x1001db3bba1afde91c1adae064fe25e) (N (L 0xffe074a8009a4a6b1e31d4be7828de) (L 0x100208676cdc37a394381f9752592ea))) (N (L 0xffdf6632d65c96298547b70f52ef07) (N (L 0x1001fcd1dc1eee027bea5c6035538c0) (L 0xffe1c703d84c58c35d6234e633ce7f)))) (N (N (L 0x1001c02b331ef857cffbd1fc85e00e8) (N (L 0xffe6a8db1501ba2a3fd3b78b7f21a4) (L 0x100166583fee2bb1a887bbe0e938b77))) (N (L 0xffeca55a3f8c0a51e99d06e8d96359) (N (L 0x100105d6fae92b815fed78575b0060f) (L 0xfff27362839b52babfb00a5ab70ed0))))) (N (N (N (L 0x1000afddc6c4d1f12d736b0e3f01583) (N (L 0xfff741f752be634078e4454b085a42) (L 0x10006d23dcaeb2ffd448656cd05adba))) (N (L 0xfffac69ca52526f53d8e6a1d816760) (N (L 0x10003ede699285d985b523bccfea3a4) (L 0xfffd189d3d9677f3dcef356dd94b11)))) (N (N (L 0x100021c0ee6adc94a553829d8878cd7) (N (L 0xfffe7e23e04fca1910266cc0837d8d) (L 0x100010f3f9a93fe28c48b0d40b8bc05))) (N (L 0xffff44508625d9f3352be664839f12) (N (L 0x100007fe034e9a69845b26f91e5c794) (L 0xffffaa2d6a9be7112e7851e11896ca))))))) (N (N (N (N (N (L 0x1000038c1f317113884cb0d472324b9) (N (L 0xffffdafff8e7a11127bbc08cc2a415) (L 0x1000017c89ec9568765f8424da0128e))) (N (L 0xfffff0eba65ef0a98c802ea1d6e176) (N (L 0x10000096ee15b3938ffc9ef1e0f0d8c) (L 0xfffffa2d18a1953e22095997dff6be)))) (N (N (L 0x10000038cac5e541ad206e915314f92) (N (L 0xfffffddd212849fcc44c276e9a40e2) (L 0x1000001451462256282787254415ece))) (N (L 0xffffff4116f4491770cb934040591c) (N (L 0x10000006eca900a82809be6ade49154) (L 0xffffffc0732d4c1ff0d20d45836b4b))))) (N (N (N (L 0x10000002409a1c796048dfd04cf904d) (N (L 0xffffffebcad444ce959e0c694138f0) (L 0x10000000b34f90d5a29730018926a89))) (N (L 0xfffffff9da0d7ab04f25c0af3560fc) (N (L 0x1000000035656e592774af960ffda6d) (L 0xfffffffe351738fabfb8cd718e93fb)))) (N (N (L 0x100000000f3fb320a1a752bff42f9c3) (N (L 0xffffffff7f976cc87dc554e2c95e92) (L 0x10000000042e9c05fa92c163bcbb95f))) (N (L 0xffffffffdd78b0919747c92fdc3eb3) (N (L 0x10000000011a58e442b61a7b7b1a2fe) (L 0xfffffffff710f7c374964f119afe99)))))) (N (N (N (N (L 0x100000000047b10f2065fc88edc0c88) (N (L 0xfffffffffdc5f2d08f4f879165d933) (L 0x1000000000118be443a387575b09d86))) (N (L 0xffffffffff76f6f57d4e9988ae2efd) (N (L 0x10000000000424ddb260e374fe241c4) (L 0xffffffffffe0320bfc2f0c06834536)))) (N (N (L 0x100000000000f205015a596f5ba5f66) (N (L 0xfffffffffff8ddc21cf280300ddb28) (L 0x1000000000003562ad475952beca8b2))) (N (L 0xfffffffffffe73bee707d46369b079) (N (L 0x1000000000000b658ef1b1c024e49fb) (L 0xffffffffffffacc0dc475fb086db97))))) (N (N (N (L 0x100000000000025b4f941a953f258a4) (N (L 0xffffffffffffef0d6bca087f88f7cb) (L 0x1000000000000078f205b3c1c215e1f))) (N (L 0xfffffffffffffca760da0302f10cd7) (N (L 0x10000000000000178619f6d9f361b4a) (L 0xffffffffffffff5bd7170b6536b607)))) (N (N (L 0x10000000000000047145e3517eedfc2) (N (L 0xffffffffffffffe171982411d59282) (L 0x1000000000000000d0af5edaaf87330))) (N (L 0xfffffffffffffffa78befca7280647) (N (L 0x1000000000000000253b97c2fcff8b9) (L 0xffffffffffffffff06f43115cde2a1)))))))

private def cneg_lf_214 : FastDTree := dleaf cneg_bt_214 0xfffffffffff9794dda6315525da7da 0x1000000000000a97d1ad9df1177d949 0x10000000000004686d6416d4d77293c 0x1000000000000378d3888572830f198 0x68f451b7c8166492a8b 0x59c764d905b6eaaf52 (M 0xfffffffffffaa0280e59ea4e9f5336 0xffffffffffff999f72d39283e53559 0x1000000000000333953e34c7a848f49 0x10000000000003f82db46e50a0aef80 0xffffffffffedf4281a3ae21b52b7a9 0x100000000000d959e19c2a1ce587d9d 0xfffffffffff6c686e90274bf3556d2 0x10000000000321e49151cb48782f2c6 0x51986190b49d6d1042 (Z (Q 0x4e1a68301f8b29961df 0x145b940ba9937149e51e 0x32f5cbf0657ed297e469) (Q 0x5f2a31d0f7c262b1d9c 0x190674847b8b1ac01db0 0x32f5cbf0657ed297e469))) (M 0xfffffffffffcac983ee5c61fe93453 0xfffffffffffe8f0c5ee5b55fc16467 0x100000000000012519fea8aff160cfd 0x1000000000000445c8da089c5a81fb6 0xfffffffffff19fe4a6f88d21613810 0x10000000000040448201f343417ea0b 0xffffffffffee13c1a285754f6306e0 0x100000000001b969a9c7c0134083863 0x46c64e84c949a26f8c (Q 0x39fe932a0d49a931bfe 0xeed11586e89ca09a9c9 0x20e622d891169a0b07ea)) (M 0xfffffffffffe2fad2c107ead519ce2 0xfffffffffffe662b58d5e30d52899a 0xfffffffffffffa4ec1da016c3343da 0x10000000000003ff0d248c744d63fee 0xfffffffffff6280544f974dccae046 0xffffffffffff2bd71998a455786a05 0xffffffffffee9e1bd180f9793af949 0x100000000000c60189983896b71e072 0x4031d49aae8e768de3 (Q 0x26b52547650d912f15f 0x9e0e54b4aaba622b920 0x155673aedec8a49358c2)) (M 0xffffffffffff29e0fc1513e27eb930 0xfffffffffffea493e9e2dc560582ca 0xffffffffffffeab73cb40a5be03496 0x1000000000000375b4811f7a0ffe7b6 0xfffffffffffa0a1285b8d811088b4b 0xfffffffffffd4b68cba73e0c8da7b1 0xfffffffffff29202e1c78b842b75ce 0x10000000000038ca69427f72347c5fc 0x3b4f04b47482879536 (Q 0x1981b5722aeb935dcbe 0x68bc03f9a987deb7350 0xde40a43d0f65f4c23d2))

private def cneg_bt_216 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xffffffffed84c2ef48dc80879978cd) (L 0x100000000af47f50b30f933df284f17))) (N (L 0xfffffffb90be146ed1fdd4067522e6) (N (L 0x10000001607ab69a786f82ba1f7577e) (L 0xffffffa696bceeda984f7a546e88e1)))) (N (N (L 0x10000013473c62d61524c94d698c6d0) (N (L 0xfffffc5eaac952b3de405470be8750) (L 0x1000009bdee2de1272ababca6b1c418))) (N (L 0xffffe85d689d0c7e9972abd3438758) (N (L 0x100003472e0a8c5b3a180ef907c7077) (L 0xffff948aa6fe05043dd5e4c391fb85))))) (N (N (N (L 0x10000ccd5c3a6bf491dd109ac508bae) (N (L 0xfffe92671e7401d73871f47aca19eb) (L 0x10002664df506d5ed82e4e0e1c62398))) (N (L 0xfffc2fc2db5877bfa345a720845930) (N (L 0x10005c13006ff189a0a4cbf06b4a78e) (L 0xfff7b99aced57db888d0c4347c854a)))) (N (N (L 0x1000b5fa4fad57f681664a5e51c8bac) (N (L 0xfff10460acec774d3407fe6a2c8159) (L 0x10012f69fa8429be024c591132f5596))) (N (L 0xffe8e3c4ee21ad7e90b154663af4f1) (N (L 0x1001b2bfe2c16796c4ca445535029f4) (L 0xffe11f8a62fc4fa895c5d7991161be)))))) (N (N (N (N (L 0x10021f76471116a05712863701ef2f7) (N (L 0xffdbc6460110a5ea00d21efd264bdd) (L 0x1002581ec2b2efd43b3c4181fa8dfd9))) (N (L 0xffda4046f7ad9148456ed0040ddc0e) (N (L 0x10024f8df65fba5bf67de0debcd44c6) (L 0xffdcb90c4ae70b08a4aa3e3237dd51)))) (N (N (L 0x10020d2f32771f7c914a0ef56de593a) (N (L 0xffe2307d1debc85edf387b1e6de623) (L 0x1001a72dc847c46decb7e77b57c2622))) (N (L 0xffe90eb581764f4f426cc3eca34e1b) (N (L 0x1001378d5cddb0ba227789a26f62999) (L 0xffefd188612efa6413bc8ed2ebc4e3))))) (N (N (N (L 0x1000d2cd6239a38f8f7e8d091f3b9db) (N (L 0xfff57ba66b1ec85254d3deb6b9d056) (L 0x100083c42de356d9b4f972359f9bf43))) (N (L 0xfff9ab9f0de58befefef23d48dcc88) (N (L 0x10004c707cc5fc444fa4ff19bfe451b) (L 0xfffc7501b908e6ea4fe2e4c961c7ec)))) (N (N (L 0x10002952f6bdf61c225693d6a530799) (N (L 0xfffe25fc9d4942f47bf5eefa6e2197) (L 0x100014e57d3f3b67c1540dc7df9b978))) (N (L 0xffff17e225f96d814cf9afed80817c) (N (L 0x100009eac1e90fe92c893dd18adc3d6) (L 0xffff9528a6e21f38b38f28792c2ca4))))))) (N (N (N (N (N (L 0x1000046e356e6f6989fc572cdd04622) (N (L 0xffffd1a39ff65ee082e343a9825af2) (L 0x100001de567adf80e191b18f122f743))) (N (L 0xffffecfc230a096cae450d870e74cd) (N (L 0x100000beeb8f9c8859ff01f5557e103) (L 0xfffff89c2ec26d9445eecd4ae19d48)))) (N (N (L 0x1000004849767e04aab283be9055a65) (N (L 0xfffffd45c924c1850003157af75080) (L 0x1000001a04f16bcb45eca7b929e179b))) (N (L 0xffffff0ac60f3882e5294bd5ffd6d4) (N (L 0x10000008ebd6161d5ad9cd8351e133e) (L 0xffffffade155408850c4fbdea38d8f))))) (N (N (N (L 0x10000002eb4ade078a0243132d7744b) (N (L 0xffffffe5bbbc188373f955ecb76639) (L 0x10000000e9c1051a70d0cdf0cbce962))) (N (L 0xfffffff7f638e00e6d09c5ee818059) (N (L 0x100000004602cc294101678244e4f21) (L 0xfffffffda494159cc12870d1c7a0bf)))) (N (N (L 0x10000000141b8d1e0a2af86ffc026c3) (N (L 0xffffffff5632f2799f59f3ede89d31) (L 0x10000000058baf246be75bc718db456))) (N (L 0xffffffffd21601dcf617deb10480cc) (N (L 0x1000000001787c848724d1f57963b9d) (L 0xfffffffff40e0ee526ceef407ed920)))))) (N (N (N (N (L 0x1000000000601e76d2f5050941d0870) (N (L 0xfffffffffd01a47bee860852b3784c) (L 0x100000000017a706ae4fd52dd9e0b6b))) (N (L 0xffffffffff46c85aa54d50cb7e8ec0) (N (L 0x1000000000059db0b1f15a6b5b5c17f) (L 0xffffffffffd4c8c33fe786e3dd7c8b)))) (N (N (L 0x10000000000149b883d9c4c169dc832) (N (L 0xfffffffffff64176bc1befff862ed4) (L 0x100000000000491c7662bf566cf6670))) (N (L 0xfffffffffffddfed1b25a27c058645) (N (L 0x1000000000000fb03ebd70ca8ee4f6d) (L 0xffffffffffff8d1c70ec2680f2be0f))))) (N (N (N (L 0x1000000000000342c065fc56ca19353) (N (L 0xffffffffffffe87ddba1750c6495dc) (L 0x10000000000000a8305b5aee49e451e))) (N (L 0xfffffffffffffb55c7ae599d9cdacf) (N (L 0x1000000000000020e05fd3e77db60aa) (L 0xffffffffffffff1a01112c08d67c6d)))) (N (N (L 0x10000000000000063d4ec37c96bf151) (N (L 0xffffffffffffffd4fa64eec5db9e9f) (L 0x1000000000000001268997f817507ba))) (N (L 0xfffffffffffffff82da835d20dbd5f) (N (L 0x100000000000000034ce36627b76043) (L 0xfffffffffffffffe9df05b6421c553)))))))

private def cneg_lf_216 : FastDTree := dleaf cneg_bt_216 0xfffffffffff981cf29415c44c0b9d1 0x10000000000009ef68df7171fcda3fb 0x1000000000000488575a3ebb5d96d84 0x10000000000003bdc57620ce616a510 0x685c60aeed6b27c3030 0x5e0966d6dbb94ea303 (M 0xfffffffffffaa9d0d1299ac1cdd625 0xffffffffffff91edcf6aa25e5a4755 0x1000000000000355d9ff2be0e4e88fa 0x10000000000004393993c7e482b1638 0xffffffffffede6b8d492bf2c901443 0x100000000000d6a3ebeb086fa82ff4e 0xfffffffffff67be8b8660b175f1240 0x1000000000031fc1f1f64cd37f6a158 0x561bdb1d9f6512ae4d (Z (Q 0x4d8cf00f45e890bb089 0x144e160c2081f3197d61 0x32e1f270c0b029760d38) (Q 0x5e962b6c69cf17561b6 0x18f5b074e138ccd9f9bf 0x32e1f270c0b029760d38))) (M 0xfffffffffffcb6f1354f8a318cac10 0xfffffffffffe8c2d5a3a52df252e4f 0x100000000000014c55448c68cf82c87 0x10000000000004813664c24f4747e06 0xfffffffffff1a0fb1d02b033904ddb 0x1000000000003e2d88dbdf50245c10f 0xffffffffffede9179b962aeb963f18 0x100000000001b6bc882d87ba1bc704b 0x4b029ac4671679bc6e (Q 0x397953b97411f387ca1 0xee327e64d5227f9368a 0x20d9ad9ac9992cbd0da8)) (M 0xfffffffffffe395b9a2cb52491add4 0xfffffffffffe66cffb96583233b82a 0xfffffffffffffd0d6bc01c9af763af 0x10000000000004373713915a8e5450a 0xfffffffffff630971e3f27a19432ab 0xffffffffffff14ed1ab5403848ee4a 0xffffffffffee8b7529a367c5d26556 0x100000000000c381699599decc3bdcd 0x43842eb6289b798419 (Q 0x263aa92aaa2cabe7e15 0x9da63745b2c132fc2ce 0x154e9d5dfdddd1628707)) (M 0xffffffffffff3249ecaa053f46e759 0xfffffffffffea77fa46430e9403af6 0xffffffffffffedb57459299a967f3c 0x10000000000003ac4ae62101c90d80f 0xfffffffffffa15339e88ee6faeed33 0xfffffffffffd3d896fe150d7663e07 0xfffffffffff28ed88182350e6d963d 0x10000000000036ccfe94043590e37ee 0x3d8cdb467c16efda8b (Q 0x1913f4f50150bf46dfc 0x6877067305daf5d51ee 0xddf1b0631aa2dc03d1a))

private def cneg_bt_218 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xffffffffed5f0ff64a763a28ceb5f1) (L 0x100000000b20377255e406513a5c41a))) (N (L 0xfffffffb76bab38586bfc891ef06c1) (N (L 0x100000016b0c2af6f01020ae2fc8a27) (L 0xffffffa34bd325158eca917b7eff83)))) (N (N (L 0x100000141dc4156639a2436d70872f4) (N (L 0xfffffc30433262a562b780d044a7a8) (L 0x100000a4a2db4f3d18ef4533abf7277))) (N (L 0xffffe6e3e78162d42bc052bcc638fc) (N (L 0x100003809717c8d297d7828cc7752f4) (L 0xffff8c8e6db779f99688939aa829d7))))) (N (N (N (L 0x10000dd3db56579da5f058ba621fccc) (N (L 0xfffe730b77e66601150e6fb2c8cbad) (L 0x100029e6c24444570981618f681fc6b))) (N (L 0xfffbd138d49696696fc36cdb9c4d4d) (N (L 0x1000657cf6d246c5f9142b817d4eadd) (L 0xfff6d5bd817084652d9a2881679df6)))) (N (N (L 0x1000ca81c11eed5027e4881bab518a3) (N (L 0xffef3fd43ed442886341d5eca98e3d) (L 0x100154c319e24955f2ab6b2244943db))) (N (L 0xffe5edaf535e81a577436f2c08ca5a) (N (L 0x1001ec9f7f79ac2a48c7a46c05ba38f) (L 0xffdcdc600b7279adac5f66bc5804b9)))))) (N (N (N (N (L 0x10026d2173bc3e7cbe6c50c4dd926d2) (N (L 0xffd66c3dcf53f869354e893bfa0403) (L 0x1002b3a39275018a773ce2090433a8c))) (N (L 0xffd450ef3e633f00a714853e8600e6) (N (L 0x1002af532ddb3fe2033b9d9fed512ac) (L 0xffd6d92602bdc8b0a5b0225160ddc3)))) (N (N (L 0x1002670d531bd4c197040b741d18578) (N (L 0xffdcf3e56c4bccd536c880bed5d957) (L 0x1001f36ce535eadcaec8d522d3773dc))) (N (L 0xffe4d23696b599f5035993898b764d) (N (L 0x100172765c50f9ae9c04bfc902cbe64) (L 0xffecb00324bd8498a204fa32287135))))) (N (N (N (L 0x1000fc82deb62479672b2a8bfb315b9) (N (L 0xfff35b44fe712fabe26aaa9cc41da9) (L 0x10009ef9ed20a69fc9ee4b6bff23d2a))) (N (L 0xfff85614de7a23c96f18072c637c3d) (N (L 0x10005ce03350a121a64e9b9b2953e88) (L 0xfffbae276238a2cb91d99aaf808f08)))) (N (N (L 0x1000328eaf5430f590f7f0fddd31d2c) (N (L 0xfffdba19c3beb80213df8d1927e7d1) (L 0x100019bd3022bc3aa299aed797b0627))) (N (L 0xfffee1231ac076b56a87f1d365be32) (N (L 0x10000c4bed4c4340c5bf3a8fa4c9236) (L 0xffff7b167e8b9419e0b8df66a458ce))))))) (N (N (N (N (N (L 0x100005878fb750ab1fe78d5636e4393) (N (L 0xffffc5f3ccca663ea5b13a50b307bf) (L 0x10000258d547358846f72a05afdb700))) (N (L 0xffffe80a2bc548d477886842656d1d) (N (L 0x100000f154000fc7d16d0ab82711d77) (L 0xfffff6a13cee77851538af95e515d7)))) (N (N (L 0x1000005bf0e1e3ef9bb9b0e8281fdce) (N (L 0xfffffc85397e248115e2b2ef610f0d) (L 0x100000214bd7db0e14fd6c67226fc6f))) (N (L 0xfffffec53de7efff64a4181e8e15f9) (N (L 0x1000000b7c306d986dad9f0ae7f24f7) (L 0xffffff95f70f15ee7069b54ed0ee01))))) (N (N (N (L 0x10000003c7c5a6b02b3764e1ecb0975) (N (L 0xffffffdde2463e5d80b779c412ed42) (L 0x10000001307e24cf34f86797a703e2a))) (N (L 0xfffffff57fbe1d62286ff7e707c505) (N (L 0x100000005bb9661d40ad372082b65f5) (L 0xfffffffce72d4349de32ecc8f23afb)))) (N (N (L 0x100000001a7e6e0399007e6e8afe3ee) (N (L 0xffffffff1fa3c9dd2cfffdbfe64001) (L 0x10000000075917ed795af9b991b6f28))) (N (L 0xffffffffc2fe946d602688f3e8f025) (N (L 0x1000000001f59d82eb0a635e1cb5566) (L 0xfffffffff00a8ab463efc1c1f7a228)))))) (N (N (N (N (L 0x100000000080c4458da22600c428c55) (N (L 0xfffffffffbfa8f482493308a45bcf3) (L 0x10000000001fdb913e6d43367b3b8dd))) (N (L 0xffffffffff05dc6f02a511b619f1cb) (N (L 0x1000000000079acaaa9b1b882a3cee3) (L 0xffffffffffc5538153243b9656a0d6)))) (N (N (L 0x100000000001c0d6824dc71df88a86e) (N (L 0xfffffffffff2b362f83ff4b54c3f03) (L 0x100000000000640b361016632839634))) (N (L 0xfffffffffffd15932bef138ae19153) (N (L 0x1000000000001594235c50bb45b5d25) (L 0xffffffffffff619267cae196080e7c))))) (N (N (N (L 0x100000000000048206684b5c52d95cf) (N (L 0xffffffffffffdf6afead86f421bdb3) (L 0x10000000000000e9b15f4be99d006d2))) (N (L 0xfffffffffffff98083c8bf37a5bedb) (N (L 0x100000000000002de8c7120f6a4bb78) (L 0xfffffffffffffebe088e9bd5357fa1)))) (N (N (L 0x1000000000000008c18df4501b89490) (N (L 0xffffffffffffffc37a4feac41a2ac4) (L 0x10000000000000019f5c44472c0c461))) (N (L 0xfffffffffffffff4f168c73f4ca212) (N (L 0x10000000000000004ad416a3c66711e) (L 0xfffffffffffffffe091148e1f21242)))))))

private def cneg_lf_218 : FastDTree := dleaf cneg_bt_218 0xfffffffffff98ae76bcf9e9982db30 0x1000000000000941a5608d2ecd63413 0x10000000000004b0e4fe19a671f11a4 0x10000000000003f8c4dad6f3348535b 0x67bb74f09d1d702949e 0x6258ae20419c1f33d2 (M 0xfffffffffffab4077821e9daaf9f2d 0xffffffffffff89e105af54a4429691 0x1000000000000380b41d6413e8bee94 0x10000000000004706e3f6e451c48aea 0xffffffffffedd9cbfc321c472417e8 0x100000000000d3f3a18dcfeae429889 0xfffffffffff6322beff70dbe579054 0x1000000000031d9d21b858951828bfc 0x5a79fc3871fe805808 (Z (Q 0x4cf8ca53eca97a3a2ee 0x1440b08d5384040c18c4 0x32ce47d984933abb92a7) (Q 0x5df9ddf36912a8f2075 0x18e50eb51f060e54d7d8 0x32ce47d984933abb92a7))) (M 0xfffffffffffcc1cb080f243118ba2e 0xfffffffffffe88e7a481cb086579eb 0x100000000000017c05357b433014f5b 0x10000000000004b2fa172a5ddb63c56 0xfffffffffff1a261b44d9614959512 0x1000000000003c1c4817628b7d31c31 0xffffffffffedbf1d8d0a5a090d65ee 0x100000000001b410df9312952fcdce6 0x4ed97f5b5fac163d3c (Q 0x38f02fbbd74e83101ff 0xed94cd517984cf9aba3 0x20cd54ab8132c8a62a47)) (M 0xfffffffffffe43835bf836495ffef9 0xfffffffffffe67030d24115d9f5041 0x100000000000000512e63a8f796db01 0x1000000000000465d9902f24e69304c 0xfffffffffff639537d0ff2c4422cb2 0xfffffffffffefe5445ca01a2d26e80 0xffffffffffee794bee8f0349dcff7a 0x100000000000c104bfd9f0319089e26 0x465e08210c58af3b3d (Q 0x25c05677d0e37ff965a 0x9d3e7966a32a4860b86 0x1546d7d3bbfad838e66c)) (M 0xffffffffffff3b2897c236737cd896 0xfffffffffffea9f09b592de7c6d3e9 0xfffffffffffff136955a47f47302f8 0x10000000000003d973509daad1d1d00 0xfffffffffffa2065a1049e36c05191 0xfffffffffffd2feb92f1a6b5cfd9b0 0xfffffffffff28bfef0a3c7412743fe 0x10000000000034d3c736c3725c7fdb4 0x3f578c227885566d71 (Q 0x18aa7bbddb38a8c942f 0x68322b9b5cf4ef5aeda 0xdda35757ed9f62c8bb4))

private def cneg_bt_220 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xffffffffed395cfd4c0ff3ca03f314) (L 0x100000000b4c48678a4451abc5d1b9a))) (N (L 0xfffffffb5c4fe7203349f0617859a5) (N (L 0x1000000175db63cb8520404f8aeb3d2) (L 0xffffff9fe7ba32cdca87f107408ae9)))) (N (N (L 0x10000014fc2b680d0cac6a3d7f4c9a6) (N (L 0xfffffbffd8e701e2b4d65a954fda8a) (L 0x100000add6851ade09795334f0e7e4e))) (N (L 0xffffe5553c82fc8a9fa6d08a0298fa) (N (L 0x100003bd92596426f8302c70a811e67) (L 0xffff8406c41906e2739c5b97c0365a))))) (N (N (N (L 0x10000eedcda7ce4ba19be89493a37cf) (N (L 0xfffe512ea9b09a2e09b1b50772f849) (L 0x10002db57245380425f72e108d8cf31))) (N (L 0xfffb6a11e366ff5f998e3dfe707ea1) (N (L 0x10006fcfaff6d118026eea5a329461d) (L 0xfff5daa3a1ec509c22be329229b61b)))) (N (N (L 0x1000e13d0b7e6a295f5736dfb77f658) (N (L 0xffed485b736a97757ffa1256759c71) (L 0x10017e817d655de75e14bd0a8f6f5df))) (N (L 0xffe29a83bd3278cfb745d26082071f) (N (L 0x10022de4ef77ca6a1eb5087da666357) (L 0xffd8084d2f64f27f61448ba65c165d)))))) (N (N (N (N (L 0x1002c57eeb345715202c84f9765eebb) (N (L 0xffd04ede0a163b1ea8e55214f01e74) (L 0x10031ca5a1523807e88403b6af088fb))) (N (L 0xffcd7a6ac57b44b3c8d8538f7b989d) (N (L 0x10031e1e5ec7aa07373993d352dc421) (L 0xffd006506231512e5cbe4e666d3d23)))) (N (N (L 0x1002cfda2f51ce8333f4211102be907) (N (L 0xffd6d2679ea32bb7a9d88d9e801b79) (L 0x10024d0976e495c8196fe10d7e2579b))) (N (L 0xffdfd2bbe4d4328be13283a266c669) (N (L 0x1001b83a2b9697a371f9ecbca05b0f9) (L 0xffe8f74099eee5ed0921521f671cc7))))) (N (N (N (L 0x10012e460caf8bcd72327911430ced3) (N (L 0xfff0cf666577378ddcd748718a9134) (L 0x1000bfad3f8a6b17d5fccf14dcef587))) (N (L 0xfff6ba27d40bdede61a7879c40139d) (N (L 0x100070c507d6b0a34d4079d01295459) (L 0xfffabca0a5421ce03f2537acb3d491)))) (N (N (L 0x10003dcf9de6f29338adcef5d94d721) (N (L 0xfffd3627ef29440acd990f10895508) (L 0x10001fae7f2698b15a79e17b0972fbf))) (N (L 0xfffe9dba72db08ae94f42dac518028) (N (L 0x10000f3c7f977a89795f563fbaefc47) (L 0xffff5ac5ed7a3749b1bfa8838facd5))))))) (N (N (N (N (N (L 0x100006e57066384c6aa1990107fa165) (N (L 0xffffb75f35f9a3b2ac681a81b1a9bd) (L 0x100002f2266963d84f57f6cf5be1667))) (N (L 0xffffe1d49bee43d101f57e4a3c20dd) (N (L 0x10000130d247f5f5eabbe8db39a2dc5) (L 0xfffff420b0e13262f7cd1b9ddd48fd)))) (N (N (L 0x10000074da1c3137152d0184c75e5c2) (N (L 0xfffffb906719fa5c7e25304c1824d5) (L 0x1000002a9397d385e909e51bd788442))) (N (L 0xfffffe6c4c5db90005c460a98340c2) (N (L 0x1000000ec650c66106b3069455c3ecf) (L 0xffffff77306703ea95fa36abc32a99))))) (N (N (N (L 0x10000004e459085632ea16bd43b2a43) (N (L 0xffffffd3b8fb07cfdb04f9b85e32a0) (L 0x100000018c558fea3cd4908f50ad162))) (N (L 0xfffffff24acbd1c3f5f6132ad6717a) (N (L 0x1000000078142b4540f0a8c8bd58977) (L 0xfffffffbef22597d0b18476a709fff)))) (N (N (L 0x1000000022e1975613bb5591bf4d1e5) (N (L 0xfffffffed7c81de7d1487cbb403239) (L 0x1000000009ba828e8465be50d3a1a68))) (N (L 0xffffffffaf019bd17e1d6024fa36e5) (N (L 0x10000000029bcde657d5e8025836609) (L 0xffffffffeab2164d99fbeabc84a18e)))))) (N (N (N (N (L 0x1000000000ac5dcb7ce04ea915b5f40) (N (L 0xfffffffffa9a43ee741f6cbac15a34) (L 0x10000000002ae005d5d59e6819541dc))) (N (L 0xfffffffffeae7450f52fa1cfb8c102) (N (L 0x10000000000a4a0d2bc64f6f94559a9) (L 0xffffffffffb067349319a59c573798)))) (N (N (L 0x100000000002627e79ffb888b6e15cf) (N (L 0xffffffffffeddd0e43ef5f04d4bed3) (L 0x10000000000088c957d9e19c5b1411b))) (N (L 0xfffffffffffc00ccd7f60bf3392fc7) (N (L 0x1000000000001da7f4f149b9d8d7e23) (L 0xffffffffffff25b635bf20eed0c00f))))) (N (N (N (L 0x100000000000063a1a4c927f83438c0) (N (L 0xffffffffffffd2e1149a0db55ad6bc) (L 0x100000000000014470be0a714fcfa05))) (N (L 0xfffffffffffff6f4c53accd36a6382) (N (L 0x10000000000000400e2e4427f6ec212) (L 0xfffffffffffffe3da8fa07bf71e710)))) (N (N (L 0x100000000000000c4706d8a2aca1bc3) (N (L 0xffffffffffffffaaee0892c82ffda8) (L 0x100000000000000249419ea6aca4ecc))) (N (L 0xfffffffffffffff061ebbdcb4bd7b9) (N (L 0x100000000000000069f279c4633d4c5) (L 0xfffffffffffffffd3633b646aae61f)))))))

private def cneg_lf_220 : FastDTree := dleaf cneg_bt_220 0xfffffffffff9947df1f9329b269e20 0x100000000000088d5ebd0b265b1257e 0x10000000000004e08303bea71f5bbc5 0x1000000000000428cc7a0ce480a1dad 0x67131882001221ae1e2 0x668ee0126fa46ba732 (M 0xfffffffffffabeb3943b25e0605aae 0xffffffffffff8166af1be5cf675d68 0x10000000000003b2912f4e2d171f1bf 0x100000000000049cc7027af46ab81c9 0xffffffffffedcd5dbc6c6d4aa11f2d 0x100000000000d148dfd1fb3082b4b62 0xfffffffffff5e94cdd5e0a6c7e677a 0x1000000000031b763cb0ac63f59ec9c 0x5e95ee9997508a3b9e (Z (Q 0x4c5fd581e35cbf778dd 0x143362fdd7748ebfcfed 0x32bacb4635758f316d52) (Q 0x5d56f32c4d5a2f2845a 0x18d48e31e347d64b6a85 0x32bacb4635758f316d52))) (M 0xfffffffffffccd0db483f65ba3d5c2 0xfffffffffffe8529220e9b8c9685cf 0x10000000000001b299539c841d4cf2a 0x10000000000004da107e666894af083 0xfffffffffff1a41575c494f12e8d82 0x1000000000003a109848928dec89181 0xffffffffffed95d0437876d80130c4 0x100000000001b166baa33e88e641020 0x523ec39125f5f82ffe (Q 0x38653d5d7c4da49a7e9 0xecf8038647072d10af7 0x20c11783cbf55d1a094d)) (M 0xfffffffffffe4e0cc1afa412abaf7e 0xfffffffffffe66b2c239e8198d7d42 0x1000000000000040122acd82f806c94 0x1000000000000489f2a6b67f73b3f86 0xfffffffffff642382441a8343028c7 0xfffffffffffee80a1304505420f8f4 0xffffffffffee679d867635de999468 0x100000000000be8b8b1d82826a4cb2f 0x48bbabcf6004235d5a (Q 0x25486729ac1428a2916 0x9cd727f8ed61249ca7c 0x153f22c58ddb0adaef2a)) (M 0xffffffffffff44658baa3255b69e8b 0xfffffffffffeabd553725e7cd6f8b3 0xfffffffffffff521da506dedd69787 0x10000000000003fc2d7f90cdc5c144b 0xfffffffffffa2ba6e2d8266b00cba3 0xfffffffffffd228cc231e813492b05 0xfffffffffff28974310cd78f22645f 0x10000000000032deba8b4e1c2906017 0x40ae8942ef6ab27830 (Q 0x184787aa705198ab43b 0x67ed88a0b377bdc4899 0xdd5596e96772b894136))

private def cneg_sub_22 : FastDTree := (dsplit (dsplit (dsplit cneg_lf_206 cneg_lf_208) (dsplit cneg_lf_210 cneg_lf_212)) (dsplit (dsplit cneg_lf_214 cneg_lf_216) (dsplit cneg_lf_218 cneg_lf_220)))

private def cneg_node_23 : FastDTree := dsplit cneg_sub_21 cneg_sub_22

private def cneg_node_24 : FastDTree := dsplit cneg_node_20 cneg_node_23

private theorem cneg_ok_18 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f true cneg_sub_18 12 4 = true := by
  decide

private theorem cneg_ok_19 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f true cneg_sub_19 13 4 = true := by
  decide

private theorem cneg_nok_20 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f true cneg_node_20 6 3 = true := by
  rw [show cneg_node_20 = dsplit cneg_sub_18 cneg_sub_19 from rfl]
  exact checkFastDTree_dsplit _ _ _ _ _ _ _ _ _ _ cneg_sub_18 cneg_sub_19 6 3 12 13 4 rfl rfl rfl cneg_ok_18 cneg_ok_19

private theorem cneg_ok_21 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f true cneg_sub_21 14 4 = true := by
  decide

private theorem cneg_ok_22 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f true cneg_sub_22 15 4 = true := by
  decide

private theorem cneg_nok_23 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f true cneg_node_23 7 3 = true := by
  rw [show cneg_node_23 = dsplit cneg_sub_21 cneg_sub_22 from rfl]
  exact checkFastDTree_dsplit _ _ _ _ _ _ _ _ _ _ cneg_sub_21 cneg_sub_22 7 3 14 15 4 rfl rfl rfl cneg_ok_21 cneg_ok_22

private theorem cneg_nok_24 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f true cneg_node_24 3 2 = true := by
  rw [show cneg_node_24 = dsplit cneg_node_20 cneg_node_23 from rfl]
  exact checkFastDTree_dsplit _ _ _ _ _ _ _ _ _ _ cneg_node_20 cneg_node_23 3 2 6 7 3 rfl rfl rfl cneg_nok_20 cneg_nok_23

end GaussSmallBridge

theorem solution (δ : ℝ) (hd_lo : -1 ≤ δ) (hd_hi : δ ≤ -(3 / 4)) {t : ℝ}
    (hlo : -(23 / 16) ≤ t) (hhi : t ≤ -1) :
    ‖mellin (fun u : ℝ => (Real.exp (-u ^ 2 / 2) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ)))
      ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖mellin (fun u : ℝ => (Real.exp (-u ^ 2 / 2) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ)))
        ((1 / 2 : ℂ) - Complex.I)‖ := by
  apply GaussSmallBridge.sound_subtree_lit true GaussSmallBridge.cneg_node_24
    3 2 (by norm_num) GaussSmallBridge.cneg_nok_24 δ _ hlo hhi
  rw [abs_le]; norm_num [GaussSmallBridge.signB]; constructor <;> linarith

-- Prove2me | solution 1 for GaussianMellinBound.small_delta_p2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T03:33:07.490796+00:00
-- url     : https://prove2.me/submissions/8f79d20b-c65c-470c-a8be-99d6e9c5b787

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

private def cneg_bt_83 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff6806843e73b451de9e765) (L 0x100000000319c219026ebe0e4d729d9))) (N (L 0xffffffff466ee00aaa03edc0e9c616) (N (L 0x1000000022845125f9eccc3bbf15887) (L 0xfffffffa98d7b9accae0728b50ce1c)))) (N (N (L 0x10000000bca097c5e44ae597dcf58a7) (N (L 0xffffffe90e6ef1fe6014ee7f112b7d) (L 0x10000002880fbe56ffd08a167a1226f))) (N (L 0xffffffbe4f3a4afeee9a1ecf7f18ba) (N (L 0x100000062d9580127e79718cc7da082) (L 0xffffff74e5de19cf29e90f0ebb220d))))) (N (N (N (L 0x1000000b83da436d47e28c50a3aa3c6) (N (L 0xffffff19156771e59030e365fef319) (L 0x1000001131b870bd25766c0e288a397))) (N (L 0xfffffec73e9c8c49c45ca669d88cc3) (N (L 0x1000001546a58eb025561bae7d265a5) (L 0xfffffe9c392aec8e310392255eca5b)))) (N (N (L 0x100000165f281da288a68467dc3b378) (N (L 0xfffffea487d089364f72dc084a1d08) (L 0x10000014618bd87841dfa1583ff300c))) (N (L 0xfffffed796dccd4f880e29ca9978cb) (N (L 0x10000010560944f41b0ec1cb85ac4fb) (L 0xffffff20123478ac3c091e831cd61d)))))) (N (N (N (N (L 0x1000000baa3e0adf283866609345517) (N (L 0xffffff687966a27dfdca8431cc64d1) (L 0x100000077f64d8bf0c5599e0c8e6604))) (N (L 0xffffffa34a220887bb7071f9024317) (N (L 0x1000000460261dc9aa72a33fda835f6) (L 0xffffffcc4c2cd531dc7d690f60ed73)))) (N (N (L 0x1000000255f5b781e2d43b556326c80) (N (L 0xffffffe589e66ceb6747d0d452d691) (L 0x1000000125d8b197900f7514366a7b0))) (N (L 0xfffffff37f45308a9756eaf922a352) (N (L 0x1000000085ab2ad094cbefc160ef5ad) (L 0xfffffffa848c7791898e0932d744ed))))) (N (N (N (L 0x10000000388f7b92c4c8f7ee26a35f3) (N (L 0xfffffffdc24d63b86416023d7498e2) (L 0x10000000165bc1f5417ed6d4a20ac5c))) (N (L 0xffffffff247b7670bc7f585d6fa5a3) (N (L 0x100000000849df8514cc667b8adb715) (L 0xffffffffb117092114857ce8d7bc08)))) (N (N (L 0x1000000002e437e7d4ea0b551a3edce) (N (L 0xffffffffe543be548fbaaa2bb5f07a) (L 0x1000000000f3c05c9df07b88ba4380f))) (N (L 0xfffffffff76ff2cf1cfff0516b3a3d) (N (L 0x10000000004bfadaa66cb19d61c7179) (L 0xfffffffffd66907b069995d8f67cae))))))) (N (N (N (N (N (L 0x10000000001679e5225a64ad9523c8f) (N (L 0xffffffffff40111e02d2dd8b616558) (L 0x10000000000653148348bedabe98fa8))) (N (L 0xffffffffffcb4873e6f53a488a85c7) (N (L 0x100000000001b24b9ed6d89f8782f40) (L 0xfffffffffff22efc481b9f3ef2eaec)))) (N (N (L 0x1000000000006f444f6f725bc60acb8) (N (L 0xfffffffffffc89c42753e933f85c27) (L 0x1000000000001b46eca632921c83f81))) (N (L 0xffffffffffff2b577c12269a3c68e2) (N (L 0x1000000000000668c6746621ef6e03d) (L 0xffffffffffffcf0d23fefbda6189d3))))) (N (N (N (L 0x1000000000000172194bb2a778a406e) (N (L 0xfffffffffffff52d202d4f3e5d4791) (L 0x10000000000000504152ac6d87bb741))) (N (L 0xfffffffffffffdb28fcd2f28518387) (N (L 0x1000000000000010c0de14740c9e3b8) (L 0xffffffffffffff87370214b061ee3e)))) (N (N (L 0x10000000000000035ef885583652d4c) (N (L 0xffffffffffffffe820fa325299be10) (L 0x1000000000000000a79120488878ddf))) (N (L 0xfffffffffffffffb71d6ca706dd58d) (N (L 0x10000000000000001f6f27ed9d71617) (L 0xffffffffffffffff28e46d14de570e)))))) (N (N (N (N (L 0x100000000000000005b3ef4a0722dd2) (N (L 0xffffffffffffffffd99b7df76fb499) (L 0x10000000000000000100682ba9d9cc4))) (N (L 0xfffffffffffffffff95d03c4d849e2) (N (L 0x1000000000000000002ba294601549b) (L 0xfffffffffffffffffee34b823d87b1)))) (N (N (L 0x1000000000000000000733a1441624c) (N (L 0xffffffffffffffffffd1b60f6a98bb) (L 0x100000000000000000012757a84e2d8))) (N (L 0xfffffffffffffffffff8b135c555cb) (N (L 0x100000000000000000002df5a05f01e) (L 0xfffffffffffffffffffee0fd97cc45))))) (N (N (N (L 0x1000000000000000000006f3ddbfaad) (N (L 0xffffffffffffffffffffd52e120310) (L 0x100000000000000000000105ef2fa37))) (N (L 0xfffffffffffffffffffff9c873983e) (N (L 0x100000000000000000000025867e9fb) (L 0xffffffffffffffffffffff1efab740)))) (N (N (L 0x1000000000000000000000053c9ee4c) (N (L 0xffffffffffffffffffffffe0ffdee1) (L 0x100000000000000000000000b65b798))) (N (L 0xfffffffffffffffffffffffbd5fdb4) (N (L 0x10000000000000000000000018312a3) (L 0xffffffffffffffffffffffff744f14)))))))

private def cneg_lf_83 : FastDTree := dleaf cneg_bt_83 0xfffffffffffa95f5670bde5665d105 0x10000000000066bd1bdeffa01410d29 0x10000000000015008875f0c8380fc81 0xfffffffffffef7d2a6170197c5ad96 0x8662c748f9133159fa3 0x1ab71e3fc42fdf1ee49 (M 0xfffffffffffaf8f2d69a3b3698ea9f 0x1000000000004855b0c2726027f062b 0x100000000000132c85bb91ce4e1c44b 0xffffffffffff2c6d818069f0029401 0xfffffffffff85ee274b70e025584f2 0x100000000001ac8a1ddc768d6b71d0d 0x1000000000012540ad7321ea9eaca72 0x1000000000036db4d168cf513f725b8 0x174aa509f61ef2b8105 (Q 0x6c2e3b1c82c181d1500 0x1bd961b6cedc7d01a0b0 0x39d66777bbe129be9d46)) (M 0xfffffffffffc196ecfcea9600039b6 0x1000000000001ef427e69343ff8d371 0x1000000000000f7832272cb3811aa46 0xffffffffffff78ae942f27c37bc009 0xfffffffffff65815e6843225e87e03 0x100000000000f5766e1f4e78e907df8 0x10000000000004f86bc10dcebbd8833 0x100000000002510ea2acd42daa60418 0x11a16b4f368fb9f6e90 (Q 0x45aa3bda22f44fd4ac2 0x1220911204413059069d 0x25113fbb1296c787d4e1)) (M 0xfffffffffffd439f1856e3343738ea 0x100000000000084323d4f3a4430d0fe 0x1000000000000c1a458ce7f7b123816 0xffffffffffffa730c5476e0b916fc3 0xfffffffffff74f0f284358dbe4e3a6 0x1000000000007f153199244dab24288 0xfffffffffff944d9a29ea95071a6ad 0x1000000000016d9f6165161a15427eb 0xd5098cdc789463ffd9 (Q 0x2c8bf1a4caeecf5cb54 0xbc618c02a1987559e0d 0x17d277b54f38276e1e25)) (M 0xfffffffffffe3b982f0d1a22cdfc85 0xffffffffffffd2dcda8ce732e720a2 0x100000000000094e22e97838e47e065 0xffffffffffffc159d23cc3927a10de 0xfffffffffff9409aa70540b5b6a53f 0x10000000000038d799dbecc0fc90f3e 0xfffffffffff7ca2f7ffee488fffa63 0x100000000000cf368ccef1ed6c438be 0xa1876f324d93f8eb23 (Q 0x1c6a719d650bc176cd8 0x7a030b14d051f3d88e3 0xf5580c587e4fdadfaf6))

private def cneg_bt_85 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff65ab54ae8d4febf1f2488) (L 0x1000000003304fd0f6f0a826789a947))) (N (L 0xffffffff3f061fd158b7413697d13b) (N (L 0x1000000024423c95a72a6a4ee26f323) (L 0xfffffffa4579bc228e80692e0954ec)))) (N (N (L 0x10000000c9bcfd42700a6ec6dc0d472) (N (L 0xffffffe742b208f5ec6f773d8eda31) (L 0x10000002c0368f3b23ce1eb66d1f057))) (N (L 0xffffffb816f28dbb1adae366962014) (N (L 0x10000006cf96f8c736a6f61811a4773) (L 0xffffff659b5de7c6830167d877b23a))))) (N (N (N (L 0x1000000cdd5362178fb33218cd79301) (N (L 0xfffffefc63c32465024f405f7e917e) (L 0x1000001372fc010fc458a81fa8209cd))) (N (L 0xfffffe9c2080549e959fcecd60634d) (N (L 0x1000001859502540e2a3e5d3ce34662) (L 0xfffffe668cfb7663a3ad9b4f09c771)))) (N (N (L 0x10000019e33efcfb008b64e460da57d) (N (L 0xfffffe6bc5f354a0b136a330221b0a) (L 0x10000017d57dcdc5d34be1b92bc69c0))) (N (L 0xfffffea39a2f3990a47a3f7e28b05a) (N (L 0x100000134c161bc2262cace37c30e5d) (L 0xfffffef62f7fc98d52992d5e57fcb2)))))) (N (N (N (N (L 0x1000000de9d699a53ed6a9d384a5d25) (N (L 0xffffff4a6a7e8b769602451a41142d) (L 0x1000000906ca399dd11a4bd80f3950a))) (N (L 0xffffff8fe076cbab2f6440fe0bf69d) (N (L 0x1000000550c17f7e0cd03c2e05aeb81) (L 0xffffffc0ea6775c3bea28c708d365e)))) (N (N (L 0x10000002dcc15a012b08b7563a9140f) (N (L 0xffffffdf6f73649fe6107e06453a62) (L 0x100000016b242fc47c6bdf73d3011e5))) (N (L 0xfffffff07c18b1ba81bef633fbb523) (N (L 0x10000000a68d30d9dabf6d231b4d581) (L 0xfffffff92440b767ac61d61d980e9f))))) (N (N (N (L 0x10000000470a1fdce020b868f25364a) (N (L 0xfffffffd2c9cfbf8c4d11f735a9a2e) (L 0x100000001c4d27fe7eed4917a395af8))) (N (L 0xfffffffee9120390506c3a679c0a58) (N (L 0x100000000a925876c136559df7beadd) (L 0xffffffff9afa62be60c7976c839363)))) (N (N (L 0x1000000003b723f5293296ed0cf1ce9) (N (L 0xffffffffdd8560cfc7b77ad319b53c) (L 0x10000000013b7cb28eeec1ba1bedd36))) (N (L 0xfffffffff4e0b09e6ad760620934ba) (N (L 0x1000000000630a8f499c21d9dd7b421) (L 0xfffffffffc998e298d0b495672963c))))))) (N (N (N (N (N (L 0x10000000001d80a7826fec7f4d59801) (N (L 0xffffffffff0333718e21b6317a5def) (L 0x1000000000085bc564346e32c044c3f))) (N (L 0xffffffffffba1848fff19b2181aa70) (N (L 0x10000000000241d0fd271ab32a5e2ec) (L 0xffffffffffed8e8fa66c898bb977d0)))) (N (N (L 0x1000000000009503429b567902e6c77) (N (L 0xfffffffffffb5944e8b0899e155309) (L 0x10000000000024c45a1a2a837511ea9))) (N (L 0xfffffffffffee070edca505d7b9682) (N (L 0x10000000000008b1b20e60501d41d26) (L 0xffffffffffffbd64a9c16cf93a4dd0))))) (N (N (N (L 0x10000000000001f92dcc81309b61a84) (N (L 0xfffffffffffff12e1ec817e5a2b27c) (L 0x100000000000006e38d898b238bca1a))) (N (L 0xfffffffffffffcd401c04cb1a053ee) (N (L 0x1000000000000017260c7a08cefa29b) (L 0xffffffffffffff589ba293574687fa)))) (N (N (L 0x1000000000000004af84913c9d678cd) (N (L 0xffffffffffffffdeb8b0ae2920b4d7) (L 0x1000000000000000ea49a77e87e8f3f))) (N (L 0xfffffffffffffff99cc2783db4c8fa) (N (L 0x10000000000000002c34aaf00212047) (L 0xfffffffffffffffed0a09225b33ab9)))))) (N (N (N (N (L 0x10000000000000000810db91427fbf1) (N (L 0xffffffffffffffffc98bb349e40675) (L 0x1000000000000000016cb2d28727d01))) (N (L 0xfffffffffffffffff688b5486a567e) (N (L 0x1000000000000000003e69062666f38) (L 0xfffffffffffffffffe67ab65ccd57c)))) (N (N (L 0x1000000000000000000a5b6cd5c3054) (N (L 0xffffffffffffffffffbd3f856fe89d) (L 0x10000000000000000001ab0f036e970))) (N (L 0xfffffffffffffffffff5679903a32a) (N (L 0x1000000000000000000042d04537248) (L 0xfffffffffffffffffffe5da68910e6))))) (N (N (N (L 0x100000000000000000000a2938bc5b6) (N (L 0xffffffffffffffffffffc141586f24) (L 0x100000000000000000000180d1ac90c))) (N (L 0xfffffffffffffffffffff6d7b58f86) (N (L 0x1000000000000000000000376a94ee8) (L 0xfffffffffffffffffffffeb2d78e17)))) (N (N (L 0x100000000000000000000007c5f3ec7) (N (L 0xffffffffffffffffffffffd1de08bd) (L 0x100000000000000000000001100ea72))) (N (L 0xfffffffffffffffffffffff9c5a112) (N (L 0x1000000000000000000000002445f5e) (L 0xffffffffffffffffffffffff2e06f5)))))))

private def cneg_lf_85 : FastDTree := dleaf cneg_bt_85 0xfffffffffffa700dbef0d4805d2f68 0x10000000000063b93847f40478575b0 0x10000000000013f38e5d43d1ea6dc31 0xffffffffffff055bc0dcd5b777e6b6 0x85a91dd6099acbbda09 0x195dd0d54435396fec4 (M 0xfffffffffffadaa17d9438366ab349 0x10000000000045966c62f8f60f43302 0x1000000000001223868451c9f7694c9 0xffffffffffff37d1250dd5d8a249aa 0xfffffffffff7f1cb37bd7993edb3aa 0x100000000001a82bd87ae56246c1bdc 0x100000000001197b69f381da8f784a5 0x1000000000036e625cef55f0c71765e 0x16090a10821c5403133 (Q 0x6bcdb33c09cec6ab883 0x1bb5226acd43d236fa26 0x39a62276c76172e53ed6)) (M 0xfffffffffffc061390325e4291498c 0x1000000000001cbf993a20183174c3c 0x1000000000000e7bd6bfd0a633a6cb8 0xffffffffffff8077948fdddc36a5f3 0xfffffffffff613adef972588ee282c 0x100000000000f14302eeb8139ac3b9b 0xffffffffffffc5d581d2898fb8468b 0x1000000000024f51b7beff8d6524eb9 0x108841b0e8c8cb3d4ba (Q 0x45d06c93e6ab9951dfb 0x120d12175928566fec69 0x24f5498205874a3b7519)) (M 0xfffffffffffd36e7f5a392e8ba5473 0x100000000000068c502c987b22c172c 0x1000000000000b2e0228982c4723238 0xffffffffffffac2e97397151433dd2 0xfffffffffff7275cfec19c47cdc7ca 0x1000000000007b77c82691b6490024f 0xfffffffffff8e762c979579036c99a 0x1000000000016adb9ad6a5852acdacb 0xc58a7b6973289010c8 (Q 0x2d0c01c32df78c92209 0xbbd2f3f09607af1c3b0 0x17c34cfded4c442d2e68)) (M 0xfffffffffffe3292d78277ec34f070 0xffffffffffffbdf2976ab94bb93011 0x1000000000000872fee5d596c82aba7 0xffffffffffffc438bb9dd6ad056eea 0xfffffffffff92bc058c8acedb7d399 0x10000000000035f3b19edd4910dd0cd 0xfffffffffff78f3384d96d492b01cf 0x100000000000cc4980ea575b1b2f25a 0x93d0c4fdd2895e3066 (Q 0x1d221946b2ca9410d67 0x79dc15f1099309ee0cb 0xf4e42c9ddfccc2cefa2))

private def cneg_bt_87 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff6350251ea6eb8605461ab) (L 0x100000000347365c7cfe6a85e760b28))) (N (L 0xffffffff3767d2f19bf3a21045c204) (N (L 0x100000002611dc0f882a9e9873c6a9a) (L 0xfffffff9edec4fc682860dfe4df05e)))) (N (N (L 0x10000000d7a2b6b02ce67124f6d75ee) (N (L 0xffffffe557258de898e247f6d9ed75) (L 0x10000002fcbdb849b11d73d9519658c))) (N (L 0xffffffb15543cb2c5d741a83c1e45a) (N (L 0x1000000780e0039b99c7ef22b24f755) (L 0xffffff54c1657f0eb689e42f7785f3))))) (N (N (N (L 0x1000000e5ca35fb9e5a64cba6a127b4) (N (L 0xfffffedc5843122c74dcac26483aab) (L 0x10000015fbbc774c8688728aa696413))) (N (L 0xfffffe6b5f934add9ecc29b010c659) (N (L 0x1000001bd81560f2bde75a97a9d6bcc) (L 0xfffffe292681f7481276a9aee4279c)))) (N (N (L 0x1000001deeb50697f25689f9ec75f63) (N (L 0xfffffe2a1f64dbb0000a03372af614) (L 0x1000001bd96680b867e1f4eb12b16c9))) (N (L 0xfffffe66d544fac03e81194e1555d2) (N (L 0x10000016c6b6d7bb3d7e6dcece418d8) (L 0xfffffec4ba8d43dd9547eade6a0c6a)))))) (N (N (N (N (L 0x1000001094ce1058c2046ca0e3e885d) (N (L 0xffffff2694613ffad9a4bcf93abbf3) (L 0x1000000adb9f4c909a1c89d90bb4da1))) (N (L 0xffffff788408d1b33d417e22391e19) (N (L 0x10000006739d5a80df625e2482c1044) (L 0xffffffb3185727eec0ea6f4c74ee79)))) (N (N (L 0x100000038126a3b83506963d7ba2707) (N (L 0xffffffd7f5a71a1563003d04789069) (L 0x10000001c06159e345d808ed935e134))) (N (L 0xffffffecc3805718f3cc8dee6f74e5) (N (L 0x10000000cf569c4889b1839b3e83b60) (L 0xfffffff76d7e94d0fdf92fdce33726))))) (N (N (N (L 0x1000000059250d12c50fff71d2c9cf2) (N (L 0xfffffffc70b15eeae65f9742615b55) (L 0x1000000023ca9d84f99ade73fb48c24))) (N (L 0xfffffffe9de6ede278eec3be2de13b) (N (L 0x100000000d78a6c3e14a51a9c57cc4b) (L 0xffffffff7ec9f1ed4074c4945f85a7)))) (N (N (L 0x1000000004c509856c1c12fdbb98a9a) (N (L 0xffffffffd3935ed98a54b1ab37af45) (L 0x100000000197f4a3ae981e4290faa72))) (N (L 0xfffffffff191001bb12b14799f221f) (N (L 0x100000000080fb4d667fb0cc568dc20) (L 0xfffffffffb8e73d301be7ba3d23cfc))))))) (N (N (N (N (N (L 0x100000000026b06da7ba1c3cd85d188) (N (L 0xfffffffffeb358bb9fd9fc3a2fea58) (L 0x10000000000b093ef24d7f5cf57db34))) (N (L 0xffffffffffa363e9521039d56796df) (N (L 0x100000000003000994c82d60c67937c) (L 0xffffffffffe76781521b4471984fbe)))) (N (N (L 0x100000000000c75f918a017d6e42ab3) (N (L 0xfffffffffff9c1addca52dda736a93) (L 0x1000000000003182dbee38f25c75a66))) (N (L 0xfffffffffffe7b885999f4f00d0050) (N (L 0x1000000000000bc83b905bb53213f0d) (L 0xffffffffffffa573c72ab7433d59d6))))) (N (N (N (L 0x10000000000002b0e54cb824de31843) (N (L 0xffffffffffffebba7182157327da52) (L 0x10000000000000973b5865eec730991))) (N (L 0xfffffffffffffba281ca8034065fad) (N (L 0x100000000000001ff43aa3ac07fd7aa) (L 0xffffffffffffff183e2bc3448b5447)))) (N (N (L 0x100000000000000681b002dde3ede13) (N (L 0xffffffffffffffd1a6ed24ceb999fa) (L 0x10000000000000014741260eb9caba0))) (N (L 0xfffffffffffffff70d3e75d9e4e9f4) (N (L 0x10000000000000003e1af0e89b56157) (L 0xfffffffffffffffe5490a53852b972)))))) (N (N (N (N (L 0x10000000000000000b658e0760fc86c) (N (L 0xffffffffffffffffb2d7386fcd7ac3) (L 0x1000000000000000020636d20b944c1))) (N (L 0xfffffffffffffffff28308df2ee020) (N (L 0x100000000000000000592cf24f97c26) (L 0xfffffffffffffffffdb6f196558c06)))) (N (N (L 0x1000000000000000000ee15fd2eb600) (N (L 0xffffffffffffffffff9fd5a8d8f7bb) (L 0x1000000000000000000268e722344cc))) (N (L 0xfffffffffffffffffff0a749b20834) (N (L 0x100000000000000000006108834e20e) (L 0xfffffffffffffffffffd9ed0f51661))))) (N (N (N (L 0x100000000000000000000ed5ce7b256) (N (L 0xffffffffffffffffffffa426c09b02) (L 0x100000000000000000000234c9a3b8a))) (N (L 0xfffffffffffffffffffff28669b649) (N (L 0x100000000000000000000051c145bea) (L 0xfffffffffffffffffffffe133bc627)))) (N (N (L 0x10000000000000000000000b86d1233) (N (L 0xffffffffffffffffffffffbb6afbce) (L 0x100000000000000000000001957867b))) (N (L 0xfffffffffffffffffffffff6b1cb90) (N (L 0x1000000000000000000000003655310) (L 0xfffffffffffffffffffffffec4b456)))))))

private def cneg_lf_87 : FastDTree := dleaf cneg_bt_87 0xfffffffffffa4c229abd50e641ff04 0x10000000000060dc85ac0b3d6127061 0x10000000000012ec71a946b5f8667c8 0xffffffffffff12d2ef9c20130a1b66 0x85117201832a34e5859 0x1809d2bc690055d3c47 (M 0xfffffffffffabdfe0a443550f432ba 0x10000000000042fdca73381c5497f25 0x100000000000112002b9395d74895ff 0xffffffffffff4341b57c7676185e56 0xfffffffffff7895750eb28d1db0447 0x100000000001a3d8ac999b0539a0711 0x1000000000010dfb559fd8ea9ce88fb 0x1000000000036ef0208ac78445cf252 0x14cb7d31a1a833b9259 (Q 0x6b8a5df28e20b68ef99 0x1b925075526999be70cb 0x39777eed9bf02939f9e3)) (M 0xfffffffffffbf3e2562fc1f9a55147 0x1000000000001aafe20285c297c9fd2 0x1000000000000d8410133c18836cffe 0xffffffffffff88831f9ccaeb554589 0xfffffffffff5d2e6f70bd311d64f98 0x100000000000ed2081cdcd161b933c0 0xffffffffffff3fdfec87813909595a 0x1000000000024d852ab3aff957678d1 0xf712016186c74f2e99 (Q 0x460a700e3214bcc53db 0x11fa4e6b1550d97aa797 0x24da47c86482a95c8013)) (M 0xfffffffffffd2af4cd4bd6ec0249f8 0x10000000000004f80899e027690ceff 0x1000000000000a4553a3ea9469df53d 0xffffffffffffb19ae783b2ad11846a 0xfffffffffff702716539dfbeebc014 0x10000000000077edb39a6599b750efc 0xfffffffffff88d0369088ab7b67d40 0x10000000000168135def83d2df456cb 0xb6135e0fab713309eb (Q 0x2d963fb804fa24f44a3 0xbb48748cd7777d5feab 0x17b49eeefc0164324720)) (M 0xfffffffffffe2a042efc98b7a251e1 0xffffffffffffab09f93ae98dcb605b 0x100000000000079a6a2f4dfe8291142 0xffffffffffffc7a9c24d549cfc5695 0xfffffffffff918facb1997468ed095 0x1000000000003323452a30745acdb64 0xfffffffffff756b0a670dac89f8216 0x100000000000c95f1c3a9cf7eb80743 0x86105e186c767eeca2 (Q 0x1dd9a3a39c5a89e559b 0x79b42bf125a81b8fcf4 0xf4730654519f91dc340))

private def cneg_bt_89 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff60f4f58ec087201899ecf) (L 0x10000000035e75bb9498052c99c4f79))) (N (L 0xffffffff2f9328209b1ed1f97e5799) (N (L 0x1000000027f3aeb66cf0257447f55de) (L 0xfffffff9920528d421d59242978b17)))) (N (N (L 0x10000000e65bd2298b1722b5c329844) (N (L 0xffffffe349e35dbbbcc5cc1a2df81c) (L 0x100000033df265693c3b425a6b7df5c))) (N (L 0xffffffa9ff843a078d76595c024663) (N (L 0x1000000842c0cc0107cc93101f12bf6) (L 0xffffff42326d582a3e85015fcba6df))))) (N (N (N (L 0x1000001005a311cc3b40fb0ca98f7e9) (N (L 0xfffffeb8954835c5c4c7e587ccece2) (L 0x10000018d44b9f680763ab705e4178e))) (N (L 0xfffffe3449c3283eaf80ab85228a90) (N (L 0x1000001fd10abf9c264ffd44335dafd) (L 0xfffffde2f6c255e7ff8866bbf52890)))) (N (N (L 0x1000002294f831ce02c3462d7f47317) (N (L 0xfffffdde3ec854f30c7c0d0de70d40) (L 0x1000002083c371cadd02064f56418d6))) (N (L 0xfffffe1fdb081d09c2942a854a7988) (N (L 0x1000001adc4075efa8d02d8fd6e631c) (L 0xfffffe8a6155966f99071bbbdbccef)))))) (N (N (N (N (L 0x10000013be7f35d31a82ff562501cd2) (N (L 0xfffffefbe3e15e61bc466524593d9a) (L 0x1000000d0cbc9aef1662d7ab9d897eb))) (N (L 0xffffff5c6d65788ec59d5a44858962) (N (L 0x10000007d2eb55e6e6baa810665faf7) (L 0xffffffa253ee850edbb1a402f3e5e3)))) (N (N (L 0x100000044979095019d19faa2ff1bc8) (N (L 0xffffffcecf8b627d1bab23b107606a) (L 0x100000022923c6c278e4b1a20a22b01))) (N (L 0xffffffe82bd7d88b7acd5d97191290) (N (L 0x1000000101e24b68a16d315c4dea9eb) (L 0xfffffff54b8a5badc3eeb8ccf0be6a))))) (N (N (N (L 0x100000006fc38d925351b6bb193665b) (N (L 0xfffffffb84fd24e4c3c1716ad0694c) (L 0x100000002d390ef377c7ddd54cb8dd7))) (N (L 0xfffffffe3ee287f91a89ef8d866b1a) (N (L 0x1000000011268e113cac16b2e650b5f) (L 0xffffffff5ae2844a044d5d22176ab8)))) (N (N (L 0x10000000061e14e43af3b3c8e5d23bf) (N (L 0xffffffffc6d077dcb34fc17fc7f06f) (L 0x10000000020f0a058ba40744d5b82df))) (N (L 0xffffffffed49622fb4e15b242b00c8) (N (L 0x1000000000a7d125f77ece68b080186) (L 0xfffffffffa32c5caf862b098a22a3e))))))) (N (N (N (N (N (L 0x100000000032b05d8e8416eafe43ba5) (N (L 0xfffffffffe4aad99820139fc8329ff) (L 0x10000000000e8ece7b1ea00ffd8c33d))) (N (L 0xffffffffff856d526f7d984b7da7e6) (N (L 0x100000000003fbea90e3a621802ff24) (L 0xffffffffffdf3af76b7619abc994ca)))) (N (N (L 0x1000000000010a802bbcc88cd916c3c) (N (L 0xfffffffffff7a09c62d6ab9dbaad55) (L 0x100000000000429bf196aba31615416))) (N (L 0xfffffffffffdf3b71afba272a55bcc) (N (L 0x1000000000000ff3a4fbd577c81ded8) (L 0xffffffffffff85062cf1fd39bf68df))))) (N (N (N (L 0x10000000000003aa85695731424f48f) (N (L 0xffffffffffffe44c2afc14474ddde1) (L 0x10000000000000cf4cb51ca082d7ba8))) (N (L 0xfffffffffffff9ff8dee36a7a18bfc) (N (L 0x100000000000002c10edea8268812a9) (L 0xfffffffffffffebf708a2ae4f05106)))) (N (N (L 0x100000000000000906c6f315040d5b7) (N (L 0xffffffffffffffbf8347309ec20c56) (L 0x1000000000000001c8aa504351bc071))) (N (L 0xfffffffffffffff37a165c6e0253a7) (N (L 0x1000000000000000572ac9de3dde728) (L 0xfffffffffffffffda65bc46be95c7a)))))) (N (N (N (N (L 0x10000000000000001016558179e0d5d) (N (L 0xffffffffffffffff92c6b37d3e444f) (L 0x100000000000000002dfa0306580bab))) (N (L 0xffffffffffffffffecccb1ce5a1168) (N (L 0x1000000000000000007f4b336291728) (L 0xfffffffffffffffffcba8f244ac516)))) (N (N (L 0x100000000000000000155b9d9a09cce) (N (L 0xffffffffffffffffff7598fb6834ed) (L 0x100000000000000000037a419449d29))) (N (L 0xffffffffffffffffffe9cb34d1f426) (N (L 0x100000000000000000008cc7f872eba) (L 0xfffffffffffffffffffc89d0746411))))) (N (N (N (L 0x1000000000000000000015a34daa7cf) (N (L 0xffffffffffffffffffff79ae96737a) (L 0x10000000000000000000033c18136d8))) (N (L 0xffffffffffffffffffffec31108ad5) (N (L 0x1000000000000000000000787dc050b) (L 0xfffffffffffffffffffffd27e40bd8)))) (N (N (L 0x1000000000000000000000111340122) (N (L 0xffffffffffffffffffffff9a257c10) (L 0x1000000000000000000000025bb3195))) (N (L 0xfffffffffffffffffffffff21c3f8f) (N (L 0x100000000000000000000000514d35c) (L 0xfffffffffffffffffffffffe27077a)))))))

private def cneg_lf_89 : FastDTree := dleaf cneg_bt_89 0xfffffffffffa2a33d0c8b87c74dffb 0x1000000000005e2610b7f318a49bc24 0x10000000000011ec6e4f26ebedb9ce7 0xffffffffffff20588bd83ed741d793 0x84976696a9a796e5deb 0x16bae16da39e2fb0528 (M 0xfffffffffffaa30cb61f1924657bde 0x100000000000408ae4715d22f6640fd 0x10000000000010234b8550b7fb59b73 0xffffffffffff4edd735c231e4257e4 0xfffffffffff72543c11199c686c223 0x1000000000019f8fbc569d17f712322 0x10000000000102bd4d36eee78eb6e44 0x1000000000036f5f10c6c2da0c5db96 0x13920479fd5f2d818cc (Q 0x6b5f8c4816f0da2d5be 0x1b70bf8c9b61badb56fb 0x394a56bfd4e337b7be23)) (M 0xfffffffffffbe2e6fa431fde1d7488 0x10000000000018c43a9dc7e2b41a5d4 0x1000000000000c92582ac61cc3d57ed 0xffffffffffff90ebc1d5259acf90a4 0xfffffffffff59589cb27cc2cba118b 0x100000000000e90ddfb8eae29b924ce 0xfffffffffffebd79d0e31b317e22d9 0x1000000000024ba975c8edeb297ce87 0xe5c7d13efbf3400aca (Q 0x4652f90d3717f80dec7 0x11e827c83440d21643fc 0x24c01f47e34e68522ef4)) (M 0xfffffffffffd1fd7b58592a4523dc9 0x1000000000000385a841fa4d69d9bc6 0x1000000000000961da4fe87cc60ae48 0xffffffffffffb78d23647c28d63cbd 0xfffffffffff6e01f7085106f9a5cc2 0x1000000000007475d6472f9afea1c86 0xfffffffffff835957354a5a21dd6cb 0x1000000000016546caafca12cb933b9 0xa6af71b40c62088c0f (Q 0x2e24fef4c0482150183 0xbac0d7d0f4850c4a38f 0x17a65afeff26712b559f)) (M 0xfffffffffffe220358cef7d404ee69 0xffffffffffff9a1aefe3b66a376797 0x10000000000006c6285c60ce218da8a 0xffffffffffffcbc1b3d155c4013180 0xfffffffffff90825d8b73d1341a5aa 0x1000000000003065373951e143028ee 0xfffffffffff72086b3390975d14f6d 0x100000000000c6773f8bc466700140f 0x7851fa9fb4af3ee641 (Q 0x1e8ba665f1623661df7 0x798a9bba3f2ca7dcae2 0xf403df5b87d9e7e20dd))

private def cneg_bt_91 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff5e99c5feda22ba2bedbf2) (L 0x1000000003760dee3dbd781a8fc7642))) (N (L 0xffffffff27874e137d9e929dcc50f6) (N (L 0x1000000029e8359a47ac517da78a7ea) (L 0xfffffff93198cdb352f08d92444cb0)))) (N (N (L 0x10000000f5f2c2d3fefe57c76683905) (N (L 0xffffffe118ed2dbff1eb6e4e17aeb9) (L 0x10000003842658357844531954ec141))) (N (L 0xffffffa20a4ee0b1cf5f2c34c6a0a3) (N (L 0x1000000916a377b8fc76f5ff80f8afa) (L 0xffffff2dc5b792b42ca0dc6ca66574))))) (N (N (N (L 0x10000011dc8777c53ca01e8d7cc1f84) (N (L 0xfffffe90b3b7fc5624fc5d4b8885d7) (L 0x1000001c05e2dd8fbd551caed91532f))) (N (L 0xfffffdf61856fa84da76d03636ddf2) (N (L 0x1000002454013a4abae27f056f2d2aa) (L 0xfffffd92cb905243458f233084abe0)))) (N (N (L 0x10000027ec1d9b728c6de3d927263d2) (N (L 0xfffffd869de9822672cf964e1ce235) (L 0x10000025ee6ec29c272dcf32df06008))) (N (L 0xfffffdcd0585909e1d5c09d0410c98) (N (L 0x1000001fa6a5999e3213721b67207ae) (L 0xfffffe45990ae537c40d27c469a6c8)))))) (N (N (N (N (L 0x100000177da27df9526f961da4b0428) (N (L 0xfffffec9145a38870af6e2059df444) (L 0x1000000fabbbc531ba39bb541c9b0f9))) (N (L 0xffffff3aaef7866bd704709c53d5a2) (N (L 0x100000097adeb010bc3d0aa862cb846) (L 0xffffff8e00cfe0215f4a89606e632d)))) (N (N (L 0x100000053d5c7fabcd8ee1a62a385fb) (N (L 0xffffffc39fc20ee9941e46b2b3b4b9) (L 0x10000002a9c71bc355ce1b38f4776d8))) (N (L 0xffffffe2822985da41fe9c835c4170) (N (L 0x100000014077d7f6d95a1fecfdbe6f2) (L 0xfffffff2a4cdac0d196aa9d92aa75e))))) (N (N (N (L 0x100000008bff4b6c6ed4aa1863b5ce6) (N (L 0xfffffffa5d9d8b9676f9a0dfc42a07) (L 0x1000000039169128e12dd027f80e368))) (N (L 0xfffffffdc6e2c9720c33437c4e2adc) (N (L 0x1000000015d0a4b55a3a8b0aac63b4e) (L 0xffffffff2d323ad40ce8d7e69c33ef)))) (N (N (L 0x1000000007d6cb749800a4781787655) (N (L 0xffffffffb67463c0ae7e23eac295a1) (L 0x1000000002a841e0e51f097ba9ec66b))) (N (L 0xffffffffe7c2a1c12a6af298bb1605) (N (L 0x1000000000da24ad32d6f832268dce1) (L 0xfffffffff86ea0bdaf80dde3e3c072))))))) (N (N (N (N (N (L 0x10000000004259436239fe690abe2e9) (N (L 0xfffffffffdc19cd497a48773cc7de1) (L 0x1000000000132f7649c7b97dc9130bd))) (N (L 0xffffffffff5debf00edca52e42faf4) (N (L 0x100000000005491ffcbc8c4b6231cc6) (L 0xffffffffffd4618c05fbf5fd3438d4)))) (N (N (L 0x10000000000163e47a80cde9829022a) (N (L 0xfffffffffff4c862481f19cb6d6a56) (L 0x1000000000005986ce9e74d07b0a49e))) (N (L 0xfffffffffffd3d161d9df5c9bf933d) (N (L 0x1000000000001593873f23dad15b1b9) (L 0xffffffffffff59245c7b61bc3fe29f))))) (N (N (N (L 0x10000000000004fd6012ac0f93f81c9) (N (L 0xffffffffffffda2de5c0941c3a8512) (L 0x100000000000011be181d76339a8ac9))) (N (L 0xfffffffffffff7c191db2f574d2a60) (N (L 0x100000000000003cb5ee4f2b34b8630) (L 0xfffffffffffffe4509b77bcb80ce3d)))) (N (N (L 0x100000000000000c8297dca43bf0dc3) (N (L 0xffffffffffffffa65c86057ececd42) (L 0x10000000000000027ca1acdbb393a85))) (N (L 0xffffffffffffffee7db1637de1b873) (N (L 0x10000000000000007a39260b3faeda4) (L 0xfffffffffffffffcb1fa8d02838afb)))))) (N (N (N (N (L 0x100000000000000016afa2220c73ff2) (N (L 0xffffffffffffffff6589caf29be2a9) (L 0x1000000000000000041339d8c35c615))) (N (L 0xffffffffffffffffe4b1ec1a90f3b2) (N (L 0x100000000000000000b586dfc307ece) (L 0xfffffffffffffffffb527afa7ab988)))) (N (N (L 0x1000000000000000001e9ff53d40fec) (N (L 0xffffffffffffffffff39019b395c70) (L 0x100000000000000000050376a322da4))) (N (L 0xffffffffffffffffffdfe65336cfa4) (N (L 0x10000000000000000000cc0ce9d9294) (L 0xfffffffffffffffffffaf822ebe35b))))) (N (N (N (L 0x100000000000000000001f8756f4565) (N (L 0xffffffffffffffffffff3bc555f396) (L 0x1000000000000000000004bcf20a083))) (N (L 0xffffffffffffffffffffe2e918d9b7) (N (L 0x1000000000000000000000b1675b769) (L 0xfffffffffffffffffffffbcd399d80)))) (N (N (L 0x10000000000000000000001944f515d) (N (L 0xffffffffffffffffffffff68e2a68c) (L 0x10000000000000000000000381f0778))) (N (L 0xffffffffffffffffffffffeb49e763) (N (L 0x1000000000000000000000007988d6f) (L 0xfffffffffffffffffffffffd3b375e)))))))

private def cneg_lf_91 : FastDTree := dleaf cneg_bt_91 0xfffffffffffa0a456761a35989b8a0 0x1000000000005b94b1f34efc88be662 0x10000000000010f5086b780dbbe99c2 0xffffffffffff2e050ccf0205d24065 0x84367097971c9d5ca1c 0x157149cf7b9c58b0bf5 (M 0xfffffffffffa89d59d2b319dd18621 0x1000000000003e3c9cdd1ff7ed4e75a 0x1000000000000f2ef6926b3f8c70ff8 0xffffffffffff5abad4503bc63e0fc5 0xfffffffffff6c5522ce86c164e0333 0x1000000000019b5056f4b62df44e891 0x100000000000f7be5ecc84021470616 0x1000000000036fb029f4622fe3aa9fc 0x125d2f203a021040731 (Q 0x6b486fd1c128137ac24 0x1b504a10fcf370e03639 0x391e8825e42fa9e4ba82)) (M 0xfffffffffffbd330aec4a5548e9683 0x10000000000016fb9eea8480cda8bff 0x1000000000000ba866b05c4cdca71de 0xffffffffffff99c4656d0b44e3495d 0xfffffffffff55b632601dec8594197 0x100000000000e50a3c75595507fe30d 0xfffffffffffe3e79b00862d11da9ef 0x10000000000249bf1e22ff7d90c4e2b 0xd4b4a914132b5ed7d6 (Q 0x46a4d0124b549cc3457 0x11d6854d76271b8163d1 0x24a6b86bd1a71e190ae0)) (M 0xfffffffffffd15a5ab15872f393bdc 0x100000000000023448a0380a9ba4d9c 0x10000000000008856dd44494ebcb6e8 0xffffffffffffbe1537874f274e999c 0xfffffffffff6c03d828a42b9097fdd 0x100000000000710f3a487b071f0f806 0xfffffffffff7e0f525709053b12eed 0x10000000000162760e068065b5379b8 0x977077dff379a47697 (Q 0x2eb2fc9fb51fabad5c4 0xba3b2b54a7211db37ab 0x179871b48371ad569cfd)) (M 0xfffffffffffe1aa9fded2576374e6c 0xffffffffffff8b190473dc0cb271bc 0x10000000000005f82e9d3b2a183e4c3 0xffffffffffffd08df92efdef354e43 0xfffffffffff8f92021f027e9a7cde2 0x1000000000002db88eec2640b8bd1ef 0xfffffffffff6ec976c1d8b06344086 0x100000000000c391d9bd06490a9d674 0x6aa5db89cbad59faab (Q 0x1f337bbcbf9c4bb3379 0x795ee719eba4ba89662 0xf39625207cd5ce8a659))

private def cneg_bt_93 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff5c3e966ef3be543f41915) (L 0x10000000038dfef4786ec34fc967f80))) (N (L 0xffffffff1f43737f6ad8a5a8ba6d45) (N (L 0x100000002beff3b82cbf0b8f4ecaeb2) (L 0xfffffff8cc7a926e7cd3c97a6af02c)))) (N (N (L 0x10000001067263ac8373e4b15aa4e88) (N (L 0xffffffdec22b9a535785865e30a969) (L 0x10000003cfb02203fdfe4cddeea8dd1))) (N (L 0xffffff99697883da8bdef7c1b44c05) (N (L 0x10000009fe0decd1cfb70947dbad6ce) (L 0xffffff174f10ae395ce0725f4ca767))))) (N (N (N (L 0x10000013e5e99670a982c97d92cbc36) (N (L 0xfffffe644219f94c6c70c264422c09) (L 0x1000001f9aba8cea7f76cd3ed3bd7f5))) (N (L 0xfffffdafedb255d4de997da95fb30f) (N (L 0x1000002972b885b1dcd7c414e16a155) (L 0xfffffd374b3f3fdecf310966f3b639)))) (N (N (L 0x1000002e0d396c0c20c69c61de67d5b) (N (L 0xfffffd217f16edb4a1a78e4ec978f2) (L 0x1000002c3719f6b0fc4aeecd7347d08))) (N (L 0xfffffd6c6d73cff02e52b08fc7837d) (N (L 0x1000002544064a83d47743ce9bade67) (L 0xfffffdf494ee5a3c7b638d919e73e8)))))) (N (N (N (N (L 0x1000001becde59ca494ded2b4abc246) (N (L 0xfffffe8ca71bc698ecc796296174a0) (L 0x10000012cd75e88f95d7e1ef6108b5f))) (N (L 0xffffff122df8e4682fcd6e651fc2bf) (N (L 0x1000000b7a0e2ebec9199d6546f6ed8) (L 0xffffff75632308e972253c6f86774c)))) (N (N (L 0x1000000666096451070df8cb09c990f) (N (L 0xffffffb5f51e72a56fda02b9f7d779) (L 0x10000003479997027d9646a2f927483))) (N (L 0xffffffdb88265c053dc33a70e88b07) (N (L 0x100000018de3dc73eded3f92c7ca967) (L 0xffffffef59bba0f355ebfb1100f577))))) (N (N (N (L 0x10000000af35038c960de96fea445c9) (N (L 0xfffffff8ebcbe593b82af49dfdc821) (L 0x10000000480083090f7255a0e70b5dc))) (N (L 0xfffffffd2f7910cf9faed78797d1fa) (N (L 0x100000001bb91282fb456b628b454de) (L 0xfffffffef31bec4cfa92d54a8439b1)))) (N (N (L 0x100000000a0930e77d6183d43b0e69c) (N (L 0xffffffffa180480bd49a2a83b8ec95) (L 0x10000000036d36e5f15fbe9b6f385d8))) (N (L 0xffffffffe0a1767c7c88fae7b1dca3) (N (L 0x10000000011b4cee7757371dbf2dadd) (L 0xfffffffff6232c5b0dd66b2e53262a))))))) (N (N (N (N (N (L 0x100000000056c40e5a5a7cc2b58a14e) (N (L 0xfffffffffd0e4a0cee08f8089208c4) (L 0x10000000001942a7eb21856be9f17e5))) (N (L 0xffffffffff29e2459daa01b65eec89) (N (L 0x1000000000070182f46b67f4f4c7b3f) (L 0xffffffffffc5fe8c41afe5ee624082)))) (N (N (L 0x100000000001dad243cf0a774b11cf9) (N (L 0xfffffffffff0fc5e8f6ae2a0ccf036) (L 0x100000000000783712c30e88ed342ce))) (N (L 0xfffffffffffc47be94391b0211e423) (N (L 0x1000000000001d28035a68f498d846b) (L 0xffffffffffff1dd11de18d22260f61))))) (N (N (N (L 0x10000000000006c8ea0bd0c7c452132) (N (L 0xffffffffffffcc6a2d28bcda5ffaef) (L 0x1000000000000184616f0445ab25bc0))) (N (L 0xfffffffffffff4aff03d7ece59976a) (N (L 0x10000000000000538fcbd87ecd8e1d4) (L 0xfffffffffffffd9c7d11bb7efd006b)))) (N (N (L 0x1000000000000011524fab700c5637e) (N (L 0xffffffffffffff83855a8c97dceed1) (L 0x100000000000000376a92dcf03e4213))) (N (L 0xffffffffffffffe78b325ef96c2c6b) (N (L 0x1000000000000000ab361c181eb0e27) (L 0xfffffffffffffffb5b7e1239cc78eb)))))) (N (N (N (N (L 0x10000000000000001ff5e252d9b3746) (N (L 0xffffffffffffffff25c6ee68214284) (L 0x100000000000000005c60091bd1dce0))) (N (L 0xffffffffffffffffd9351c8bca254b) (N (L 0x100000000000000001029cab76f5f2b) (L 0xfffffffffffffffff9514209e9bf6f)))) (N (N (L 0x1000000000000000002bde954022a04) (N (L 0xfffffffffffffffffee22b99aacf36) (L 0x10000000000000000007388497b55c6))) (N (L 0xffffffffffffffffffd1a4a26c0232) (N (L 0x10000000000000000001277631ae7f4) (L 0xfffffffffffffffffff8b23e635e7c))))) (N (N (N (L 0x100000000000000000002de520797a7) (N (L 0xfffffffffffffffffffee19b7ef27b) (L 0x1000000000000000000006eee3bf703))) (N (L 0xffffffffffffffffffffd552c0b681) (N (L 0x100000000000000000000104f02c536) (L 0xfffffffffffffffffffff9cf162ca7)))) (N (N (L 0x1000000000000000000000255bc6bca) (N (L 0xffffffffffffffffffffff2005f5f9) (L 0x100000000000000000000005364123d))) (N (L 0xffffffffffffffffffffffe125c947) (N (L 0x100000000000000000000000b57ebf8) (L 0xfffffffffffffffffffffffbdae5bc)))))))

private def cneg_lf_93 : FastDTree := dleaf cneg_bt_93 0xfffffffffff9ec5e66face6bfa4542 0x100000000000592704f06440f570744 0x1000000000001007f3b9a7401ae1fd4 0xffffffffffff3be8d3057ccdae655a 0x83e9e50c8c156e8f166 0x142ddf2fe49c206e890 (M 0xfffffffffffa726393dbdd3000e2d4 0x1000000000003c1196e9fb4c2681683 0x1000000000000e44c5e4c17e36aa0e4 0xffffffffffff66e851c9a81d7c2044 0xfffffffffff66948a4aeb059f20c64 0x1000000000019719f0ddd902020a387 0x100000000000ecfbc74f9f9dc816823 0x1000000000036fe46d7b5987dc6aac8 0x112e0e41daf1f90b076 (Q 0x6b402df5dd2003162f0 0x1b30d005822fe4e2a735 0x38f3f53bdb58770e0fec)) (M 0xfffffffffffbc4d0dc3a977910f0ec 0x1000000000001554c6ef41dec882127 0x1000000000000ac81985e38af3056f5 0xffffffffffffa3182746a910c3f77a 0xfffffffffff524437e3114498a0d8d 0x100000000000e114db3c891ad4203d7 0xfffffffffffdc2b896950e7862f8e6 0x10000000000247c6b135d52cd6d06b8 0xc3ef43b9b155be03ec (Q 0x46faeca9df62d69592e 0x11c55284d291cbf3bd74 0x248dfedf03c43890c3c4)) (M 0xfffffffffffd0c75730fe483eb6668 0x1000000000000102bb0dbf9ced20735 0x10000000000007b20672ffcbaa5d0bc 0xffffffffffffc53b6b0efe6d9a8bd8 0xfffffffffff6a2a5226b9b1983384d 0x1000000000006db90acfe2fb975c5f7 0xfffffffffff78f00ec5de56d35f33f 0x1000000000015fa15f5a83e5afb015b 0x886f0bbf29fae7ed8a (Q 0x2f3b719e5e8da180488 0xb9b6b21a57513018faa 0x178ad63890f722d7833d)) (M 0xfffffffffffe1413334051d471ac11 0xffffffffffff7df2fe68d450f19f9a 0x10000000000005328d9d7e063776f87 0xffffffffffffd61477cdc0462b5803 0xfffffffffff8ebcaeaef71b94349e5 0x1000000000002b1c71ad6c558fb8da2 0xfffffffffff6bac66e7ada71fce343 0x100000000000c0aee56e30aad44da44 0x5d2113c6c5ca9f9ac2 (Q 0x1fcd3a3f74af66e4aaf 0x7930b66ea6bdfb60cf8 0xf32966244e4c73453b9))

private def cneg_bt_95 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff59e366df0d59ee5295638) (L 0x1000000003a648ce44abe6cc46a6b31))) (N (L 0xffffffff16c6c7198a32ccc5d36ba6) (N (L 0x100000002e0b6dfa52b6d2c36db13bf) (L 0xfffffff8627c94289bd50d22ae160e)))) (N (N (L 0x1000000117e5fa5ecdc6b86fd58be65) (N (L 0xffffffdc436d2edeffbe06071b3dc4) (L 0x1000000420eb60299651762492597f1))) (N (L 0xffffff90100409bd40d2aec382da00) (N (L 0x1000000afaa3b25a9e53f70bc10e516) (L 0xfffffefe9e8bf62a3c49a28e823e73))))) (N (N (N (L 0x1000001626ceed62a539d515701ffe9) (N (L 0xfffffe32c3a263632f28ff7a5a2ed0) (L 0x100000239e2389e83c4c6528b995d08))) (N (L 0xfffffd60d2def0672e0b873db09b81) (N (L 0x1000002f4117db13f7e0e30e5ddb16f) (L 0xfffffcceefd2938f90896f33d59575)))) (N (N (L 0x1000003514c17b280175fb246584145) (N (L 0xfffffcace5a0a0bde3e2e5ea735498) (L 0x100000337fd95b8b9e134fa1a87ee32))) (N (L 0xfffffcfbe08512053e10746b156a85) (N (L 0x1000002bd7550e4428186779a8d2c54) (L 0xfffffd953bba6c70ad56b462974e2c)))))) (N (N (N (N (L 0x100000212b6ec231610a38d4b443687) (N (L 0xfffffe44d967dcaa5f1d56993f1ce3) (L 0x100000168a97e03ee84654c2cb7583b))) (N (L 0xfffffee19a2171d299a4f452c22553) (N (L 0x1000000de1e8215fe7e1b9eb1b358cf) (L 0xffffff57996f979111ebaa500e6d27)))) (N (N (L 0x10000007ce9db1297112067b5d61cb5) (N (L 0xffffffa5468fb34d71fdc8d50fdc40) (L 0x10000004090f64c7d37a31551a82d4b))) (N (L 0xffffffd2f1afd40f435bc002e4d95d) (N (L 0x10000001ed958057a3cb37e3fd2a9ce) (L 0xffffffeb4375c2d9ec8807f06919f6))))) (N (N (N (L 0x10000000db141db338bc04a65d7d4e9) (N (L 0xfffffff71d2dd1f8f235462ac849c5) (L 0x100000005abb24c24a0f6840308f917))) (N (L 0xfffffffc7097ca35f8a61573aeadf9) (N (L 0x100000002332fdf4f3a94cbac78d1b3) (L 0xfffffffea95349b092529a0f584b01)))) (N (N (L 0x100000000cd63816820cdb2539a6a92) (N (L 0xffffffff86b02463ff53a40b754898) (L 0x10000000046a2a82dd9e13dfb4f9ba8))) (N (L 0xffffffffd770f73e836341204968d3) (N (L 0x10000000016f9501051c44070bc6bc8) (L 0xfffffffff3289e01ff158b6ae7ffac))))))) (N (N (N (N (N (L 0x1000000000715c745a90280fd3ef07e) (N (L 0xfffffffffc23e590ba5d27723eeffa) (L 0x1000000000213a646ce8428bc0bd3f8))) (N (L 0xfffffffffee566e06845fd2b2b99de) (N (L 0x1000000000094701ecce3d3526e30d6) (L 0xffffffffffb2ef45319a9952138282)))) (N (N (L 0x10000000000278e60b4de989bb718e2) (N (L 0xffffffffffebec2c80d4df9067583c) (L 0x100000000000a1456c6ca48ccab7eee))) (N (L 0xfffffffffffafe7729281aaaea7e21) (N (L 0x100000000000275caad6c69c95ea4fd) (L 0xfffffffffffecdb09c27143c4e570f))))) (N (N (N (L 0x100000000000093787451fb7a5ae6df) (N (L 0xffffffffffffb9b52ef50474fc5040) (L 0x1000000000000212d7368bd1441e9df))) (N (L 0xfffffffffffff07da5c7d5ac90c3dd) (N (L 0x1000000000000072e74bd06b71061e7) (L 0xfffffffffffffcb49d95042159e348)))) (N (N (L 0x1000000000000017f5d80b695f2bf2c) (N (L 0xffffffffffffff534e221b228651b4) (L 0x1000000000000004d1b1c7acd4d068d))) (N (L 0xffffffffffffffdddf7ad017462837) (N (L 0x1000000000000000ef9a25dd6517973) (L 0xfffffffffffffff97bfaf01292bafd)))))) (N (N (N (N (L 0x10000000000000002cfb919a552d9f1) (N (L 0xfffffffffffffffecbfed808ceb3b6) (L 0x1000000000000000082befa87c7e8aa))) (N (L 0xffffffffffffffffc8f0d553bdec11) (N (L 0x100000000000000001701239e4b198c) (L 0xfffffffffffffffff676798fc6c566)))) (N (N (L 0x1000000000000000003ec7d1e8cf71d) (N (L 0xfffffffffffffffffe65d81ba716c3) (L 0x1000000000000000000a63b9cfdb5d6))) (N (L 0xffffffffffffffffffbd1ee18a8630) (N (L 0x10000000000000000001ab66f5a69ec) (L 0xfffffffffffffffffff5681d0e6385))))) (N (N (N (L 0x1000000000000000000042bdd799ded) (N (L 0xfffffffffffffffffffe5e6dd2df26) (L 0x100000000000000000000a229ad4a43))) (N (L 0xffffffffffffffffffffc1739c72e1) (N (L 0x10000000000000000000017f6cfc805) (L 0xfffffffffffffffffffff6e122818d)))) (N (N (L 0x1000000000000000000000372d203cb) (N (L 0xfffffffffffffffffffffeb45c3d14) (L 0x100000000000000000000007bc9a12e))) (N (L 0xffffffffffffffffffffffd2163f45) (N (L 0x1000000000000000000000010ec4694) (L 0xfffffffffffffffffffffff9cd09bf)))))))

private def cneg_lf_95 : FastDTree := dleaf cneg_bt_95 0xfffffffffff9d087a90736aaa19bdf 0x10000000000056db630d2ddd0533854 0x1000000000000f26fbbd4bba394beb5 0xffffffffffff4a0c2f249e5b84b257 0x83ad0b0317c6ea2ccc0 0x12f1f3b10b51673b664 (M 0xfffffffffffa5cc2fa048bfb10afef 0x1000000000003a0831b41f213c11539 0x1000000000000d6690672e2e0c1ce56 0xffffffffffff736c723f30bf2c4b52 0xfffffffffff610f1654f5484146587 0x10000000000192ec1c8b5ea049e7687 0x100000000000e272f00a22f0ed63a28 0x1000000000036ffcdf79375014bdc7b 0x10063029462d08e281b (Q 0x6b41f5bce80d2ec6eab 0x1b1236281da003aa6a03 0x38ca8397f64116a38463)) (M 0xfffffffffffbb7d9fb9079556b14c3 0x10000000000013ce22e8eb23a87ea22 0x10000000000009f35e0b50cef8b29dc 0xffffffffffffacea64d772c73e41f7 0xfffffffffff4effed1218aa9f5c63e 0x100000000000dd2d1c3a75312acdd85 0xfffffffffffd4a11fb0499b4b528fc 0x10000000000245c0c2761bd29d058e2 0xb3964042bce0ce979a (Q 0x47508cd9644d844d2b4 0x11b47e8fb1da8427208a 0x2475e1249d067d869826)) (M 0xfffffffffffd045e7b462d7683d214 0xfffffffffffffef859720aae42303b 0x10000000000006e9a6f979fccac1c6f 0xffffffffffffcd00720ee274bc0153 0xfffffffffff68732ce892e1d0f7673 0x1000000000006a728e34299a94cca18 0xfffffffffff73f99491a1e6b75271f 0x1000000000015cc8fe54d3f8ed4a3d8 0x79cbba7db89adf7506 (Q 0x2fba1f253779666e7ff 0xb932d8e4400a554e77a 0x177d7df4a9d068da5d24)) (M 0xfffffffffffe0e5a5f6bdd11c24371 0xffffffffffff7292bc5ef41a477f9d 0x10000000000004775c12a8a8f64805c 0xffffffffffffdc53a8613620782c67 0xfffffffffff8e009f41a6f5e02645a 0x10000000000028901dcb86e972e42cb 0xfffffffffff68af91d1cde1f226f20 0x100000000000bdce66e87ca9e282d40 0x4fdee0eb7235197f54 (Q 0x2055aa92713e06bf2fa 0x78ffcebde1ecffe9d74 0xf2bd4c526648519c07e))

private def cneg_bt_97 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff5788374f26f58865e935c) (L 0x1000000003beeb7ba274e2900783951))) (N (L 0xffffffff0e1077970312c9a0a20b48) (N (L 0x10000000303b2b381250bc73a7edbf3) (L 0xfffffff7f36fb4935680e8f20f98bf)))) (N (N (L 0x100000012a593a273372b01bd4de534) (N (L 0xffffffd99a656716556a921f4bd559) (L 0x100000047838fa8fcd6145ceaf7e983))) (N (L 0xffffff85f0164caa4331d836f722a5) (N (L 0x1000000c0e27ed1cfc3e40c43891dae) (L 0xfffffee3803b606b03e7b517d2094c))))) (N (N (N (L 0x10000018a4b290f54a2397314c59f09) (N (L 0xfffffdfbaf27e3ace90e4ae3d70628) (L 0x100000281ca3171b886077d7c0f9599))) (N (L 0xfffffd07b4d754691ed1f350ddc263) (N (L 0x10000035d56cd786a9b1c9091cc7cea) (L 0xfffffc5801a196b0b1bf4052fc14dc)))) (N (N (L 0x1000003d22fbeb56105cf994889c2f7) (N (L 0xfffffc268d6096c547666aac83a647) (L 0x1000003befc23c464ad92e00ba84378))) (N (L 0xfffffc78d65b52295a481fae13ad7b) (N (L 0x10000033891463d7e09c2b05ff118b3) (L 0xfffffd251b6c0d48706b2f03ce3f63)))))) (N (N (N (N (L 0x100000275de79396bb8035512acac31) (N (L 0xfffffdef98c5c6ba0b6f7f8db57f89) (L 0x1000001b00500623acfa1a483aebfc5))) (N (L 0xfffffea763db410fa253b9b20c29ca) (N (L 0x10000010c73bae589075be68fe1e47f) (L 0xffffff33954d7a9b0837401f8c7858)))) (N (N (L 0x10000009847e0123ea7b23da869b7f0) (N (L 0xffffff90ee39aca31ce613ce9442a6) (L 0x10000004f6008436323d035458d7d4f))) (N (L 0xffffffc861dcae26971fc39661e9f4) (N (L 0x1000000263c268f0f8227a52c9b4cfb) (L 0xffffffe6322410cc6791d1dfecda26))))) (N (N (N (L 0x1000000111b1cdd09c77e8e03834c13) (N (L 0xfffffff4dafcaf200d399075614fe5) (L 0x10000000723afba57cf20f68c6df102))) (N (L 0xfffffffb802c27ae525cbede9be48e) (N (L 0x100000002ca6d207d7fd7d5f49f3c44) (L 0xfffffffe4baff9d5631da8ee902002)))) (N (N (L 0x100000001067929bd77c7a59f625eaf) (N (L 0xffffffff64686e87ee010dbfe782ec) (L 0x1000000005aebca516a1897b36f0713))) (N (L 0xffffffffcb9b8ad9f17a4207357ce5) (N (L 0x1000000001dc8066b18a9b60bd78d4e) (L 0xffffffffef4bac728c4889c6deb2a2))))))) (N (N (N (N (N (L 0x100000000093f8e741bfe0bdd033076) (N (L 0xfffffffffaf1ce46d96257a1cb6b99) (L 0x10000000002bab2a9c388c38316bf49))) (N (L 0xfffffffffe8b5cd1759549134c7d51) (N (L 0x10000000000c461d4501cdade045e8f) (L 0xffffffffff99b52b303c6e0da9bc0a)))) (N (N (L 0x1000000000034ad097fd6fcc0712d7a) (N (L 0xffffffffffe52d4bbb6ae4089f0323) (L 0x100000000000d8254bf632bbaccd650))) (N (L 0xfffffffffff944f2c0eb74f4f38887) (N (L 0x1000000000003517029a73d227f8661) (L 0xfffffffffffe6191c23450077e18d3))))) (N (N (N (L 0x1000000000000c824a090c50fcfd17b) (N (L 0xffffffffffffa04ec4b4b2627edd88) (L 0x10000000000002d4ddabe7258470211))) (N (L 0xffffffffffffeac2093deeb770f975) (N (L 0x100000000000009dd995bd150bd7dce) (L 0xfffffffffffffb75eef835d60752b2)))) (N (N (L 0x10000000000000211c9fb8ed03acc22) (N (L 0xffffffffffffff10a4c55442d146dd) (L 0x1000000000000006b2e774e927e6c7a))) (N (L 0xffffffffffffffd06c87e6f6b396d4) (N (L 0x10000000000000014efcfb81f03ce96) (L 0xfffffffffffffff6dd448fb5d7bbd3)))))) (N (N (N (N (L 0x10000000000000003f3fdcff686c3d7) (N (L 0xfffffffffffffffe4db28463d2ede6) (L 0x10000000000000000b8e02df6f4faaf))) (N (L 0xffffffffffffffffb1edd2984a84fa) (N (L 0x1000000000000000020b5976ec80e4d) (L 0xfffffffffffffffff266eb6f30e230)))) (N (N (L 0x10000000000000000059c18830e128e) (N (L 0xfffffffffffffffffdb4042113df57) (L 0x1000000000000000000eef2d702177d))) (N (L 0xffffffffffffffffff9f9b7cb391ed) (N (L 0x1000000000000000000269a7877b42b) (L 0xfffffffffffffffffff0a68f3b9634))))) (N (N (N (L 0x1000000000000000000060f625b73ef) (N (L 0xfffffffffffffffffffd9fc429e587) (L 0x100000000000000000000ecd27433ba))) (N (L 0xffffffffffffffffffffa46aed93b5) (N (L 0x100000000000000000000232da5bc43) (L 0xfffffffffffffffffffff293ba14c6)))) (N (N (L 0x100000000000000000000051694701c) (N (L 0xfffffffffffffffffffffe156ebab9) (L 0x10000000000000000000000b79226b7))) (N (L 0xffffffffffffffffffffffbbbe049c) (N (L 0x100000000000000000000001938c1db) (L 0xfffffffffffffffffffffff6bcf0e2)))))))

private def cneg_lf_97 : FastDTree := dleaf cneg_bt_97 0xfffffffffff9b6caabfbf09b48d458 0x10000000000054afe1a23fbc1dac9ca 0x1000000000000e53ed1b0be9dcfe0c3 0xffffffffffff586fa04b5570b1e9bf 0x837b301bee64ef84c57 0x11bf523837b0d2cc673 (M 0xfffffffffffa4900933bc5e975f049 0x100000000000381e86d4ce22eb21ac3 0x1000000000000c962ba46d8b0b161ec 0xffffffffffff804609171a2143f377 0xfffffffffff5bc1a94e0c463067bc6 0x1000000000018ec6844fda7865c5be9 0x100000000000d8216c1fdca2a1ab3eb 0x1000000000036ffa84ab204d35d630e 0xee79e3978efd1b8685 (Q 0x6b49167d54b68f0f977 0x1af465286e821a842b30 0x38a21be909b9f9ab9189)) (M 0xfffffffffffbac5e76525745b37b13 0x1000000000001265da9da703335f030 0x100000000000092c1b8d3879b529d8f 0xffffffffffffb736ff450e558ee119 0xfffffffffff4be6c68cebe04c9f67d 0x100000000000d95276dbbb09af98b97 0xfffffffffffcd4639bcba6b94a5106 0x10000000000243ade94ed4447d8fab1 0xa3d0de3bfc07c35f39 (Q 0x47a1499f468bf2e0920 0x11a3fb754b1a402a396c 0x245e503a7684946aa66d)) (M 0xfffffffffffcfd77c14b2bcc06bdab 0xffffffffffffef8e2fd5606bdca8fb 0x100000000000062e47d621bdc0b99ac 0xffffffffffffd55db3d5a50fafdada 0xfffffffffff66dc5ca01e2ec9dd10e 0x100000000000673b20bf9e2a1f40c67 0xfffffffffff6f2a0b430e464e02b9a 0x10000000000159ed30e9a18ebe3b7df 0x6bb1452d4b6c750adf (Q 0x302b56aef0be78e535e 0xb8af2ccc4c074dc0695 0x1770603bc106e23ea517)) (M 0xfffffffffffe099a27b612bd8bf292 0xffffffffffff68dd3e08fbf459e2eb 0x10000000000003c8a26be5652c44aad 0xffffffffffffe342e0511b09e3c525 0xfffffffffff8d5c34e1049be1b4e59 0x1000000000002612e5c197091e22ee7 0xfffffffffff65d16889aa79b143fdf 0x100000000000baf06a40a32bae73bca 0x430416ce8a8740b2ce (Q 0x20ca3c766c45d27a4e5 0x78cc0a157309ec81e14 0xf251981622841698383))

private def cneg_sub_11 : FastDTree := (dsplit (dsplit (dsplit cneg_lf_83 cneg_lf_85) (dsplit cneg_lf_87 cneg_lf_89)) (dsplit (dsplit cneg_lf_91 cneg_lf_93) (dsplit cneg_lf_95 cneg_lf_97)))

private def cneg_bt_100 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff552d07bf409122793d07f) (L 0x1000000003d7e6fc91c9b69b0bfe9ea))) (N (L 0xffffffff051fb3acfcde5de4b10b1d) (N (L 0x10000000327fb435e678743914e686d) (L 0xfffffff77f23956512788233c3ddd1)))) (N (N (L 0x100000013dd846bf418b233fccbbbe5) (N (L 0xffffffd6c4aba95f474cb59b2cee6f) (L 0x10000004d5ff64aaced06873ee226be))) (N (L 0xffffff7afae957501a5ea7258bc544) (N (L 0x1000000d3a7f79b7ea28b216543783e) (L 0xfffffec5bbe29ae4c3a14e32c0fbcd))))) (N (N (N (L 0x1000001b658ef3d965ac4a1816f92d0) (N (L 0xfffffdbe6e032619436825b6998533) (L 0x1000002d24114f296bb573a55f82875))) (N (L 0xfffffca3618ce186e48fb4a915e23f) (N (L 0x1000003d48b10c84ae62bc8d8bc9cb6) (L 0xfffffbd0915f341bd6426388e7fd0f)))) (N (N (L 0x100000465c7b1c1e323369de479201d) (N (L 0xfffffb8be12f2584e43952019a6c03) (L 0x10000045b39e47625de472ed674431f))) (N (L 0xfffffbe063ef1dc8561313681ad312) (N (L 0x1000003c883010654c85be5aa914266) (L 0xfffffca15b2d535e0f7b78177690db)))))) (N (N (N (N (L 0x1000002eaf15d7b3f792658e855d993) (N (L 0xfffffd8a75685fc2b08dc0b9cdd222) (L 0x100000205119abd4b2d2714ca9c00af))) (N (L 0xfffffe61b0bb503c0f21dc6237d4f9) (N (L 0x1000001442db31d3625c461c1f39d49) (L 0xffffff0812b546eb503f81162b511d)))) (N (N (L 0x1000000b97c961b5099c44816145971) (N (L 0xffffff782393b94bf4f9f5711bf345) (L 0x1000000617f3573843eae4f24cdec28))) (N (L 0xffffffbb675d6e70519880368489a2) (N (L 0x10000002f59267891f3d940b304f434) (L 0xffffffdfeaef8678dd2a7f79708127))))) (N (N (N (L 0x1000000155a086e7854b717a8c71b41) (N (L 0xfffffff208fb0f06682bc1932ed63d) (L 0x100000008fb06d22009c9dd6a803cbc))) (N (L 0xfffffffa519f347548c49c90de5052) (N (L 0x1000000038979114049910c957e12da) (L 0xfffffffdd4f572362dc312b6ce62fd)))) (N (N (L 0x1000000014f1f6f8746b41518462ed5) (N (L 0xffffffff389ee380b90c83434d2046) (L 0x10000000074ed43e0e8193da3995597))) (N (L 0xffffffffbc61f0aaa60799b98a32f2) (N (L 0x1000000002692235641d35e29cb08f7) (L 0xffffffffea4a4d26432b803ba0010b))))))) (N (N (N (N (N (L 0x1000000000c0f95951ca6d6ee20246c) (N (L 0xfffffffff9627374c8b0cef247aa3a) (L 0x1000000000395638f54f863df3a8df4))) (N (L 0xfffffffffe1516d798996dae5494fb) (N (L 0x10000000001039246643235a23557af) (L 0xffffffffff78594c52c7377385ef9f)))) (N (N (L 0x100000000004614f80f9482999b6b44) (N (L 0xffffffffffdc32c748ed95f96918e9) (L 0x100000000001216bca5596ae48660b7))) (N (L 0xfffffffffff6f57d5ed7342dad2cf6) (N (L 0x1000000000004789cc21c8f07746801) (L 0xfffffffffffdcfd00a45d48d2bd57a))))) (N (N (N (L 0x10000000000010f5f61517152bbf8b4) (N (L 0xffffffffffff7dda3dd61e8b2c2bab) (L 0x10000000000003dcdee285c0b89c317))) (N (L 0xffffffffffffe2ef00f51e1aaf3bf5) (N (L 0x10000000000000d8a44dd3d7129621e) (L 0xfffffffffffff9c05c1fc732ae80dc)))) (N (N (L 0x100000000000002db707136adcf4117) (N (L 0xfffffffffffffeb4914865005afd7d) (L 0x10000000000000094d872c8cbc7c762))) (N (L 0xffffffffffffffbdbd0f719e80f869) (N (L 0x1000000000000001d3e5b4f2f6d1fc5) (L 0xfffffffffffffff33405146be5bc35)))))) (N (N (N (N (L 0x100000000000000058d929b08dee30c) (N (L 0xfffffffffffffffd9c33b8ecb9706a) (L 0x100000000000000010529942a1a42f8))) (N (L 0xffffffffffffffff91682971596905) (N (L 0x100000000000000002e769a06a09dcf) (L 0xffffffffffffffffeca1912e347c78)))) (N (N (L 0x10000000000000000080327e494b9cf) (N (L 0xfffffffffffffffffcb5e91385a2b7) (L 0x1000000000000000001572320346b12))) (N (L 0xffffffffffffffffff7534bda297e0) (N (L 0x100000000000000000037bb88e18dd4) (L 0xffffffffffffffffffe9c7f153f9a8))))) (N (N (N (L 0x100000000000000000008cb9faba1e4) (N (L 0xfffffffffffffffffffc8aeaf23878) (L 0x1000000000000000000015983921864))) (N (L 0xffffffffffffffffffff7a09f098cf) (N (L 0x1000000000000000000003396dfaa63) (L 0xffffffffffffffffffffec43c142e7)))) (N (N (L 0x1000000000000000000000780063a5a) (N (L 0xfffffffffffffffffffffd2b0fdfa0) (L 0x100000000000000000000010ff4efb3))) (N (L 0xffffffffffffffffffffff9a9faecb) (N (L 0x10000000000000000000000258d7ea6) (L 0xfffffffffffffffffffffff22cf42c)))))))

private def cneg_lf_100 : FastDTree := dleaf cneg_bt_100 0xfffffffffff99f30744ab1b412c104 0x10000000000052a2536a46d975a6685 0x1000000000000d9080922cca0184bfd 0xffffffffffff670c4507e639afaf2e 0x834fbe29ed030245295 0x10983955638289944d1 (M 0xfffffffffffa37286c6558ad3b978e 0x10000000000036526c216ad301dc973 0x1000000000000bd5571d437100d8f47 0xffffffffffff8d6ca882a40d862e43 0xfffffffffff56a95fc3741973ba6f0 0x1000000000018aa8e4fb4770be19da7 0x100000000000ce04f612bc9db34461d 0x1000000000036fde609e0501ed83f9e 0xdd4dcdf93f7a1269bb (Q 0x6b5115fb04f62a5e66d 0x1ad748fb8752739c2e32 0x387aa99cd44ce0e89779)) (M 0xfffffffffffba26f946dce17c484ac 0x1000000000001119cfc025b4ccc228c 0x10000000000008741f4963910fba705 0xffffffffffffc1f2cf16fda4330fa7 0xfffffffffff48f669e84a440ac2825 0x100000000000d58474e51be3bcf814d 0xfffffffffffc618d5d82b000530857 0x100000000002418ebf57f495c0123b6 0x94d0362c25ecd649db (Q 0x47e927f85b3b7220b45 0x1193bd9020c59d2d268a 0x24473f44ce5f60e44679)) (M 0xfffffffffffcf7d6c75bb697de1fd8 0xffffffffffffe1cc5af0ea3ae8cfb1 0x1000000000000581c3be0f3a61d5f2b 0xffffffffffffde45c081216d34c4b9 0xfffffffffff6563fe73e5ee5cb2d98 0x10000000000064123038544312e569d 0xfffffffffff6a7fb812749bf3758e0 0x100000000001570e419d1d811f41929 0x5e58a13515a23e9dab (Q 0x308bfd97db91aa4336f 0xb82b53d74362199db3b 0x176375fd7edce0ceed75)) (M 0xfffffffffffe05eb6b339cc3e2094a 0xffffffffffff60b2dc46fbcb68c58c 0x1000000000000328480c53008e47694 0xffffffffffffead2c92f9178e4c17f 0xfffffffffff8ccdf2ac30a6854d89f 0x10000000000023a42c2c1b7a582ceae 0xfffffffffff63107575faec936e403 0x100000000000b81501af9afc44ddd34 0x36c72317afdadd53e4 (Q 0x2128fc301cbd0fd8c27 0x789551db3327523d851 0xf1e61c1f987f78ae045))

private def cneg_bt_102 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff52d1d82f5a2cbc8c90da2) (L 0x1000000003f13b5112aa62ed5417cf7))) (N (L 0xfffffffefbf3aa109efb4b3d8b2a55) (N (L 0x1000000034d993a56c483bec3fb750a) (L 0xfffffff7056693cf094f5ebc052db6)))) (N (N (L 0x10000001526fb75505da2908f9f849c) (N (L 0xffffffd3bfba3a4a064cdbeb2b3b31) (L 0x100000053aaae0dfc71baacfe397a02))) (N (L 0xffffff6f20bf0519230fda9323d58b) (N (L 0x1000000e81b32584b91f8219eb07250) (L 0xfffffea514a50137675f9cd4ff2da1))))) (N (N (N (L 0x1000001e6fe86be66355ffef80cd35d) (N (L 0xfffffd7a5ad68023d059f93cf4f03c) (L 0x10000032c3ba5a2adb725eb6044bab7))) (N (L 0xfffffc3284a2dc0d8aca24508bd074) (N (L 0x10000045b6d6eaebf05d32291fc2400) (L 0xfffffb36717555ab22170720ec3e1c)))) (N (N (L 0x10000050eaa87470584c49839af927d) (N (L 0xfffffad9f0222d3bc63aceaa3addb4) (L 0x10000050feb6d7988d69ef56fea4c10))) (N (L 0xfffffb2f2d341b18502b01d79dd064) (N (L 0x100000470af622b56f6853e61d7e293) (L 0xfffffc06ab1b9875d313868f0508aa)))))) (N (N (N (N (L 0x100000375104b5da719a627cc7e99c9) (N (L 0xfffffd12925853e61475f9dfd641d1) (L 0x10000026a5ab30dec02fc2765c02d94))) (N (L 0xfffffe0e4df317008a813a3f25661f) (N (L 0x10000018725c19fa395f89a364b2a3f) (L 0xfffffed38db02676e999749ff4ae97)))) (N (N (L 0x1000000e1be378ae69dbe351a7c44aa) (N (L 0xffffff59f45d09b72540b75afa7cfe) (L 0x100000077a766247a060d1269a18af5))) (N (L 0xffffffab781fd0b2634643ca2c2ec7) (N (L 0x10000003a95483e49d5278d1505891c) (L 0xffffffd8258b0910764c9dbc2b9266))))) (N (N (N (L 0x10000001aa0cb2b6b11ede7b11c3eb3) (N (L 0xffffffee842ceb4400d0dfa1b594bf) (L 0x10000000b4961383367ab406388f728))) (N (L 0xfffffff8d538765cfe5c1cd76741bb) (N (L 0x1000000047a975522a41deafd0a0024) (L 0xfffffffd3e8cc9925b6ff589b97f62)))) (N (N (L 0x100000001ab7faf45aab31568faffae) (N (L 0xffffffff00bd5506a6c5a536c16b0a) (L 0x100000000963c5391509ca0e6282861))) (N (L 0xffffffffa8cfdfb272e6bc47cb97ab) (N (L 0x10000000031e8c1c129c8e41864152c) (L 0xffffffffe3cf894be0964903ff7940))))))) (N (N (N (N (N (L 0x1000000000fb6eb6eb045d2fd9e299a) (N (L 0xfffffffff759e42f508a02c6c58631) (L 0x10000000004b36cef3eba9a0d2d1b20))) (N (L 0xfffffffffd79defc4c140215e2f319) (N (L 0x1000000000156c6cb3b220f4011b181) (L 0xffffffffff4c4707b63c68086b2a1a)))) (N (N (L 0x100000000005d272d6bab4b88a8cee6) (N (L 0xffffffffffd0423c407e30f2f1ffca) (L 0x100000000001832d2f56bd554fa7f21))) (N (L 0xfffffffffff3dde88af66de30a2886) (N (L 0x100000000000604ea13b50b670f4b3f) (L 0xfffffffffffd0b80c27a14f2f5cd14))))) (N (N (N (L 0x10000000000016f9b3672c228fdae64) (N (L 0xffffffffffff4f28762c594b00b9a1) (L 0x1000000000000543c16f7d2bab00b47))) (N (L 0xffffffffffffd843ccf73f573d2f05) (N (L 0x10000000000001290c959e2aea43c6b) (L 0xfffffffffffff7681c23ee04c5c76e)))) (N (N (L 0x100000000000003f0e1aa835e46f73a) (N (L 0xfffffffffffffe3582409a39eaee39) (L 0x100000000000000ce8204be5496654c))) (N (L 0xffffffffffffffa3cd7d230d3ccf65) (N (L 0x10000000000000028ce9aa1fea2ea35) (L 0xffffffffffffffee1793063f6a2f8d)))))) (N (N (N (N (L 0x10000000000000007cb00b48d669766) (N (L 0xfffffffffffffffca2ff0580205c0c) (L 0x1000000000000000170927110d58318))) (N (L 0xffffffffffffffff637d0558095f8b) (N (L 0x1000000000000000041efcfc2d93fda) (L 0xffffffffffffffffe4701400771d52)))) (N (N (L 0x100000000000000000b6ecb62460620) (N (L 0xfffffffffffffffffb4b2957501fbe) (L 0x1000000000000000001ec4689d8a5a1))) (N (L 0xffffffffffffffffff38590d93257f) (N (L 0x100000000000000000050623e2132c9) (L 0xffffffffffffffffffdfde4e2aed96))))) (N (N (N (L 0x10000000000000000000cc0ba8276f6) (N (L 0xfffffffffffffffffffaf95190b2ee) (L 0x100000000000000000001f798b3bb65))) (N (L 0xffffffffffffffffffff3c3df4ff45) (N (L 0x1000000000000000000004b94f79bd0) (L 0xffffffffffffffffffffe30327e71b)))) (N (N (L 0x1000000000000000000000b0b5b99da) (N (L 0xfffffffffffffffffffffbd1c6febf) (L 0x1000000000000000000000192802cb5))) (N (L 0xffffffffffffffffffffff6995ce5d) (N (L 0x1000000000000000000000037db66aa) (L 0xffffffffffffffffffffffeb62d9df)))))))

private def cneg_lf_102 : FastDTree := dleaf cneg_bt_102 0xfffffffffff989c08162f4d3943f6d 0x10000000000050b04cdd55b2aa60133 0x1000000000000cde47f987552754ebf 0xffffffffffff75d47958aeee0f0b57 0x8326509ba26b5d781cf 0xf7f55b145ad29a5f14 (M 0xfffffffffffa2744d5581619c8a652 0x10000000000034a1785105e9ae2fc57 0x1000000000000b25a99d3c48204126b 0xffffffffffff9ad13fbc20bd5d90fd 0xfffffffffff51c38bf1cfa0f92985d 0x1000000000018693094fb6f42d5b320 0x100000000000c41b6d5127eb8ab9230 0x1000000000036fa9742106d68543138 0xcd0eb9897ecf8e7cb7 (Q 0x6b55c4e7f99ea2d8c51 0x1abad04ab5befecdba91 0x38541a8e124e1504e927)) (M 0xfffffffffffb9a1c7e3c12ae37af5a 0x1000000000000fe7a32062083bcaafa 0x10000000000007cd0a69192eaec6b77 0xffffffffffffcd0c430d15c138cb35 0xfffffffffff462ca9c26e660040ef0 0x100000000000d1c2ae4b921d8b2e5bd 0xfffffffffffbf171296dd6a5f8310a 0x1000000000023f63deca4c6c01dac13 0x86d0cd40634b8231a9 (Q 0x4824a6424d9063d72c2 0x1183bb175cd95ea562ce 0x2430a342d4965d0d3a7d)) (M 0xfffffffffffcf38e9dc0da1ae0f564 0xffffffffffffd58dd7845bc690cb88 0x10000000000004e5c64040a410d6dfe 0xffffffffffffe7a4f088cc25fc5c39 0xfffffffffff6408550f223378f1154 0x10000000000060f7381a394ac4b54f4 0xfffffffffff65f8fc20b264701fcae 0x100000000001542c7e00b702f8fbe45 0x520f577279e301131f (Q 0x30d98eae40cc0d617aa 0xb7a7073cd6c14b109f0 0x1756b98318a1000adf49)) (M 0xfffffffffffe0364529de10f4e5225 0xffffffffffff59efab4c24b1260270 0x1000000000000298026b97ec530bb14 0xfffffffffffff2ee0106b5f8e05898 0xfffffffffff8c547ad03d0cd779575 0x10000000000021436061e8acda265ec 0xfffffffffff606b5adaae3649a9d80 0x100000000000b53c441f1d63bbdfbf1 0x2b82e85e66f7ed9448 (Q 0x217088b6b293e190068 0x785b9ab454ab17b764d 0xf17ab9c6fd12c4469d9))

private def cneg_bt_104 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff5076a89f73c8569fe4ac6) (L 0x10000000040ae8792516e786dfcf273))) (N (L 0xfffffffef28b897710cf5356bb2822) (N (L 0x10000000374956256308eba5273191f) (L 0xfffffff68605c3f35d69308ce7058b)))) (N (N (L 0x10000001682c998d09b4965557c1b84) (N (L 0xffffffd088ed28ff241ec03236ebef) (L 0x10000005a6adc66c415604885741ad6))) (N (L 0xffffff6250d300caa1f2c215377f3b) (N (L 0x1000000fe5f207bc120e7ed35f07a5b) (L 0xfffffe8148ae304b30fce1f39cd507))))) (N (N (N (L 0x10000021cad87e80614b010e0eb278d) (N (L 0xfffffd2ec03be614638cd07ebbbc6f) (L 0x100000390c82a0eb23c3e34eb4fc08c))) (N (L 0xfffffbb3a3d7c2c4c0c900a7fc691a) (N (L 0x1000004f3f1ec0df7745a5783b60d65) (L 0xfffffa872ea1a8baee538482e0d5db)))) (N (N (L 0x1000005cfc5fb0ea0d7a60467d19d03) (N (L 0xfffffa0d617227ba09017bb5fc146f) (L 0x1000005e0bbb22f488b3d2c4369b4eb))) (N (L 0xfffffa6154bf84dd6ebf126017a28b) (N (L 0x100000535034173ad6ccd5abb61f16c) (L 0xfffffb5131993a4aca2eafa6895af6)))))) (N (N (N (N (L 0x100000417e2b722521d7be27d1bf777) (N (L 0xfffffc84930853e36e608bf63b029e) (L 0x1000002e2e0c61699ea95da931ec824))) (N (L 0xfffffdaaa062d6ec08c7be3694d29a) (N (L 0x1000001d78f96cfd218f9b1cbc46ab4) (L 0xfffffe94361bfa31f512905fdc6976)))) (N (N (L 0x10000011281929f4f3fe0d722760494) (N (L 0xffffff353c2d25938f89ee8b2837da) (L 0x100000092b8c3cee45fa8d514b3508d))) (N (L 0xffffff97ec09fb0d1418b1d1987008) (N (L 0x1000000486bf56c72f315d9f5bd037d) (L 0xffffffce8932722a991da00e4dea80))))) (N (N (N (L 0x1000000212dfd5870dd03523eac3084) (N (L 0xffffffea2144dddacb5694517ae3f0) (L 0x10000000e2c26c663e980d4d9168920))) (N (L 0xfffffff6f75afb1b87d5d8f8b7c4d0) (N (L 0x100000005aaa2ee3ce865a8ae99eb50) (L 0xfffffffc802d177120e951588f2ab4)))) (N (N (L 0x10000000220da7284ead8bedb1a5488) (N (L 0xfffffffeb97cebeb1330dfd9591ae6) (L 0x100000000c0dc3ca1a345a83ee2b559))) (N (L 0xffffffff8fad9972626fce61d1c4cc) (N (L 0x1000000004085baa8afdd445705e092) (L 0xffffffffdb6e2aefc7d05a056ed188))))))) (N (N (N (N (N (L 0x1000000001474d80e730bbd3552cabf) (N (L 0xfffffffff4b3f534e1d1bd4a79bf15) (L 0x100000000062934a0982214231784fe))) (N (L 0xfffffffffcae5a9a806e24a7cbbfb6) (N (L 0x10000000001c43cc460d802bf636bf3) (L 0xffffffffff121b6998ad0d97c1e227)))) (N (N (L 0x100000000007bb4770da113d1e08031) (N (L 0xffffffffffc0656fc57d1ac5bbca3d) (L 0x10000000000205783238858a29d22ec))) (N (L 0xffffffffffefbb79ec8aae6aae6ef3) (N (L 0x1000000000008187ecc43fe6e64d892) (L 0xfffffffffffc035a95bec7c66e5e02))))) (N (N (N (L 0x1000000000001f17ffdb65b19d8f488) (N (L 0xffffffffffff0fef9f14a8570f4375) (L 0x100000000000072b2938713c9e9e98d))) (N (L 0xffffffffffffc9bb385c49e473a2f0) (N (L 0x1000000000000196ea53264a5f1da3c) (L 0xfffffffffffff4317c0855f6ea0f54)))) (N (N (L 0x1000000000000056e3dbdcbac0d11cc) (N (L 0xfffffffffffffd8657cfdaced7eebf) (L 0x1000000000000011e3c6384ea4d8733))) (N (L 0xffffffffffffff7fd66372e549d080) (N (L 0x10000000000000038e377c60d635dcb) (L 0xffffffffffffffe6f6aa58e026a285)))))) (N (N (N (N (L 0x1000000000000000aed0efe05caaa32) (N (L 0xfffffffffffffffb457187977f5eb2) (L 0x1000000000000000207a80f4535e475))) (N (L 0xffffffffffffffff22b7b838077371) (N (L 0x100000000000000005d7b4bf8daef2e) (L 0xffffffffffffffffd8d104f1fdf123)))) (N (N (L 0x10000000000000000104c34136a8ded) (N (L 0xfffffffffffffffff945d1fe2a01e1) (L 0x1000000000000000002c18c88ebde3e))) (N (L 0xfffffffffffffffffee115704400d7) (N (L 0x100000000000000000073d361503382) (L 0xffffffffffffffffffd1942126b6dc))))) (N (N (N (L 0x100000000000000000012790e68c6a3) (N (L 0xfffffffffffffffffff8b352f4f502) (L 0x100000000000000000002dd49d88a2d))) (N (L 0xfffffffffffffffffffee237de2754) (N (L 0x1000000000000000000006e9fc1ecae) (L 0xffffffffffffffffffffd576cec46a)))) (N (N (L 0x100000000000000000000103f5f3b2d) (N (L 0xfffffffffffffffffffff9d596fd16) (L 0x10000000000000000000002531efbaf))) (N (L 0xffffffffffffffffffffff210b9bcf) (N (L 0x1000000000000000000000053005bbb) (L 0xffffffffffffffffffffffe14ae7fd)))))))

private def cneg_lf_104 : FastDTree := dleaf cneg_bt_104 0xfffffffffff9767fdce67bbbbc104c 0x1000000000004ed72b2dc723635cdaf 0x1000000000000c3e9d92e59ca591907 0xffffffffffff84b49b68b5bba905bf 0x82fac8a9b15f14efccd 0xe77b9300b85eafad30 (M 0xfffffffffffa195d74b4e6efd007e0 0x10000000000033090a36fd8f4beb271 0x1000000000000a8880e02cb094ed9fd 0xffffffffffffa85edf6d93bc1a4c6b 0xfffffffffff4d0db149b564ef881d8 0x1000000000018284c63a72282ef2fcb 0x100000000000ba62d3d2cd863247c3f 0x1000000000036f5cbbf58d6cec83297 0xbdf40d5234d5f933a8 (Q 0x6b53510733b11de048b 0x1a9eebfb003ca63bf4d8 0x382e5eba1dff2b8ff9a8)) (M 0xfffffffffffb937158be657512b469 0x1000000000000eccbc59d5e7629665b 0x100000000000073842418c2423c5aba 0xffffffffffffd86c240250d517c608 0xfffffffffff438781d585ac30fa53c 0x100000000000ce0cc5c1fa5d9ad4da8 0xfffffffffffb83f2cca65aa340adee 0x1000000000023d2de12cac96584e9c5 0x7a1bf93da9383a3a6b (Q 0x4850c617f98f0337f15 0x1173ebc0b5dab34c3163 0x241a72cb981ace3b4881)) (M 0xfffffffffffcf0af066a97cd373c5d 0xffffffffffffcaa9f997b1e1b21247 0x100000000000045bbc953ea192e1c40 0xfffffffffffff1622845d94baa2c81 0xfffffffffff62c7c52dc18075f3e27 0x1000000000005de9be78f93595a36a5 0xfffffffffff619452b69370c5a5dd3 0x100000000001514835653f31fb52661 0x4740060da41d30d8c2 (Q 0x311218e296cc515c539 0xb7220f20c910e77b3d1 0x174a2634f9c95927e7a4)) (M 0xfffffffffffe02177a6b60b4160126 0xffffffffffff546c01fbdc3e2244cb 0x10000000000002194669e72178077b9 0xfffffffffffffb79dda28ccef652a9 0xfffffffffff8bee8b7bb099f7bb262 0x1000000000001eeffba83f5cb9726f5 0xfffffffffff5de0d15c3f717bcf6ea 0x100000000000b2664be6d09d077ad50 0x21e2584d5a32e4f1a8 (Q 0x21a00acbc9042e0baa0 0x781ee1b5988c45c8b53 0xf10f5dfe7c4ac8d4a75))

private def cneg_bt_106 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff4e1b790f8d63f0b3387e9) (L 0x100000000424ee74c90f4467af24a68))) (N (L 0xfffffffee8e6809579c037dbcbc376) (N (L 0x1000000039cf8a41ac31f1bb3ddc851) (L 0xfffffff600ccec5b2ed7a17b296879)))) (N (N (L 0x100000017f1c748efe82b49e38adf48) (N (L 0xffffffcd1d81348adfbdfed34783b6) (L 0x100000061a80c9df33eec94806e3193))) (N (L 0xffffff54794c1b6b5c271a5846daaf) (N (L 0x100000116993fc5f3dca736f74f9131) (L 0xfffffe5a10d4e9fe1c83333b4541cf))))) (N (N (N (L 0x100000257e1a019e7aa4a4acf997fd2) (N (L 0xfffffcdad7574954adb95561054383) (L 0x10000040110e3cc2e1c8c6fa45c069d))) (N (L 0xfffffb251b1595eed789c8fbcb9623) (N (L 0x1000005a047493a2c033759a5c03b7a) (L 0xfffff9c007bfda2b6e1646bc7c216d)))) (N (N (L 0x1000006ac69c8e26b95353b465157ac) (N (L 0xfffff92266dc097bf9b53fac225c38) (L 0x1000006d1dc4af4a6e367dbcf5641be))) (N (L 0xfffff972692d540d0479da704837d4) (N (L 0x10000061a07d1c200886a9628b10ba3) (L 0xfffffa7c75d01a8134be60bd5e5690)))))) (N (N (N (N (L 0x1000004d7acaace629cd4836896ec0c) (N (L 0xfffffbdc85eb5a760587ae9dfc8a2f) (L 0x1000003722dbacb0b9e78b13d1e44ad))) (N (L 0xfffffd3391e639d8406217039bdedb) (N (L 0x10000023809f0558c8b3f40b7ce2ad9) (L 0xfffffe47e12b11fdb60d0939801dcf)))) (N (N (L 0x10000014d864a9762241f4a91ebd4d4) (N (L 0xffffff089a5c83da3481ad7607959d) (L 0x1000000b3c2d47594c3006fc3f5c242))) (N (L 0xffffff7ff69e7b8d7da5b760817f32) (N (L 0x10000005973f0d5fe1ab85033970eb2) (L 0xffffffc2a90262e62cc5146a72fc06))))) (N (N (N (L 0x1000000294eb8478fc4171738d011e7) (N (L 0xffffffe4aab5a455e00bda10de0e01) (L 0x100000011c7da4a2d945067467f0843))) (N (L 0xfffffff49f940db69f6a791a524522) (N (L 0x10000000729b21e374294ad0bd1d6c1) (L 0xfffffffb8f6e2232c2ffc30cd2390f)))) (N (N (L 0x100000002b5cf1a0a706b8c0b9104ee) (N (L 0xfffffffe5eb7f718966c0784dc1034) (L 0x100000000f75b9054e308a48015759f))) (N (L 0xffffffff6f6da3a684f1e08aaa1b6c) (N (L 0x1000000005356df29d4c9064cdf2347) (L 0xffffffffd099f1dba81d99e0f62b70))))))) (N (N (N (N (N (L 0x1000000001a9ae9ba65b52b0f840084) (N (L 0xfffffffff141df7e82db66a71d9e1a) (L 0x100000000081133892eb1c8a067ff04))) (N (L 0xfffffffffba3c0795c0e7ef8fd9dfa) (N (L 0x10000000002541b7f73739e729bf7b7) (L 0xfffffffffec565c591418454782274)))) (N (N (L 0x10000000000a420477d8fd1a0c0e893) (N (L 0xffffffffffab5764c87c57a1d99041) (L 0x100000000002b2f84176f4f62ac4e93))) (N (L 0xffffffffffea358b96504e39f8a4c2) (N (L 0x100000000000ae0df0effeb4b656454) (L 0xfffffffffffaa0409e88cb063502dd))))) (N (N (N (L 0x1000000000002a0a9d70cf0aaa827fc) (N (L 0xfffffffffffeba6a9bb6c2732b03df) (L 0x10000000000009c07dce57af5d15eb9))) (N (L 0xffffffffffffb5f39e1fadbf5c5299) (N (L 0x100000000000022ce457f1874035ad7) (L 0xffffffffffffefcb298f5b6524d3d5)))) (N (N (L 0x10000000000000779f22befbd2c107c) (N (L 0xfffffffffffffc951595e76c94e498) (L 0x1000000000000018c5e6da6c6dfd047))) (N (L 0xffffffffffffff4e0304fb032b27d3) (N (L 0x1000000000000004f3b68c4e557298c) (L 0xffffffffffffffdd07dd000d7c8e29)))))) (N (N (N (N (L 0x1000000000000000f4dd258cdd48e34) (N (L 0xfffffffffffffff95b9b49aef699b8) (L 0x10000000000000002dbf89eb3754334))) (N (L 0xfffffffffffffffec771497c72fa3a) (N (L 0x100000000000000008467e703853d25) (L 0xffffffffffffffffc85949338c3867)))) (N (N (L 0x100000000000000001735d2e6e89c86) (N (L 0xfffffffffffffffff664b78801da42) (L 0x1000000000000000003f23e3856d93f))) (N (L 0xfffffffffffffffffe6413d4785f0a) (N (L 0x1000000000000000000a6bb835dd638) (L 0xffffffffffffffffffbcffbe39d899))))) (N (N (N (L 0x10000000000000000001abb845d6a74) (N (L 0xfffffffffffffffffff568b91ba213) (L 0x1000000000000000000042ab3dde64d))) (N (L 0xfffffffffffffffffffe5f33c6be07) (N (L 0x100000000000000000000a1c12bff8c) (L 0xffffffffffffffffffffc1a5105f1a)))) (N (N (L 0x10000000000000000000017e0ec7edb) (N (L 0xfffffffffffffffffffff6ea607d5e) (L 0x100000000000000000000036f0eabed))) (N (L 0xfffffffffffffffffffffeb5d8d84d) (N (L 0x100000000000000000000007b37282d) (L 0xffffffffffffffffffffffd24d478e)))))))

private def cneg_lf_106 : FastDTree := dleaf cneg_bt_106 0xfffffffffff9657049465d1b8918b6 0x1000000000004d141d898190422b6dd 0x1000000000000bb295f70931962cfb0 0xffffffffffff9393f0380a488ff509 0x82c95f8764f81cfb413 0xd84ca1209592b210f4 (M 0xfffffffffffa0d767b100a459f0200 0x100000000000318652365a662461859 0x10000000000009fef3c9feb74c0f8f4 0xffffffffffffb5fb9d823c768e4664 0xfffffffffff4885800972fce7e7efc 0x1000000000017e7df7c3a7e417221b2 0x100000000000b0d94bc7c071ea5a86a 0x1000000000036ef92fb8680c24f82a5 0xb03ba0b6c36ff076a1 (Q 0x6b46547d42c14066dc6 0x1a838ecadd93268cba96 0x380967fdd11b93b6b826)) (M 0xfffffffffffb8e76810683dcb71632 0x1000000000000dc653a47a002736366 0x10000000000006b6e31a9a73d0dfe05 0xffffffffffffe3f677418baa471082 0xfffffffffff4105131b578ae8a2309 0x100000000000ca6265ef84885dafc0c 0xfffffffffffb18f7d821233fae8e77 0x1000000000023aed5e36297280e9a98 0x6f07ab7f25732eeffa (Q 0x486b12ee595ac0156d6 0x1164487788bf5423e450 0x2404a5d2ca3ae572c309)) (M 0xfffffffffffcef43b79765ba0118a0 0xffffffffffffc0f50ed6ccd9ccc36e 0x10000000000003e4c8e9fc1b510d3e4 0xfffffffffffffb5fb8fff155575532 0xfffffffffff61a0d236a8b9eba5d49 0x1000000000005ae9517de23ade83868 0xfffffffffff5d504f8e419777b5a7d 0x1000000000014e61b7be3af501e3da4 0x3e78bc01f638375b00 (Q 0x31343c7e70db880a731 0xb69c3f7d6a352bb1854 0x173db86878e66f3dac33)) (M 0xfffffffffffe02133bdaa53dbeae55 0xffffffffffff4ffd2102e0bf02bd76 0x10000000000001ad3c14f765c72dbfb 0x100000000000004574c7d8e5bdc5f04 0xfffffffffff8b9afbde25c729e52cd 0x1000000000001ca97ef712174b9170b 0xfffffffffff5b6fa689f4e8714b868 0x100000000000af9335b6c9240cd7ee0 0x1b2d5f69ebd57eb99d (Q 0x21b72cf565e077f1837 0x77df2a959f59f1aa857 0xf0a3fec2d947f315026))

private def cneg_bt_108 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff4bc0497fa6ff8ac68c50c) (L 0x10000000043f4d43fe93798fc2184d1))) (N (L 0xfffffffedf03be210133ba7847bb80) (N (L 0x100000003c6cc0734b6952c569f50ff) (L 0xfffffff57586816cb0381ed30c37bc)))) (N (N (L 0x10000001974d4c1d1bfdb1bf833201b) (N (L 0xffffffc97a92a9ec6d3176d46fa299) (L 0x1000000696a34834aa89d0e9cb7860d))) (N (L 0xffffff45872cf5502dd67c3801e786) (N (L 0x100000130f1c42780d88bc385abe7f7) (L 0xfffffe2f2037f786718a0a21000550))))) (N (N (N (L 0x1000002992161f36d00bf94a98ec983) (N (L 0xfffffc7dc64b5aca7839c241de6534) (L 0x10000047e5ebe76bf0d2618936e634c))) (N (L 0xfffffa85182120a3da5d1bb8d3771f) (N (L 0x100000662dd7b07e558e34cb7432213) (L 0xfffff8dde4ab6bb05a331873e28fc4)))) (N (N (L 0x1000007a853cd8871eed2c29fd19db5) (N (L 0xfffff814ad525671a55c2b766796a7) (L 0x1000007e817dd11853a46fd3f50a43d))) (N (L 0xfffff85d4ff8687d0ebd4385311304) (N (L 0x100000724f9f1d1049157d769658e50) (L 0xfffff98346fd7122bd6cf0a52995b3)))))) (N (N (N (N (L 0x1000005b967ff83ddff6f84b1af3af9) (N (L 0xfffffb15cb958561d70f9ca850df75) (L 0x10000041c6c9c97cc0ef0742d1d966b))) (N (L 0xfffffca57b642675bc15c130fd9dce) (N (L 0x1000002abb249555eec3ae1fcf2f024) (L 0xfffffdebf83771ac69ce5376968606)))) (N (N (L 0x100000194e56c8395abd3b416bed504) (N (L 0xfffffed265f4880ed4f1561237113c) (L 0x1000000dc0e3682f327b0412fb7a8ba))) (N (L 0xffffff629f50e5253a59b1f12fe663) (N (L 0x10000006e653e7af3a5f6e10be263f7) (L 0xffffffb3ff85773242cc5e65d2fd05))))) (N (N (N (L 0x10000003361de0b88837ccd64f435fe) (N (L 0xffffffddde538f8c731bceafb53f70) (L 0x10000001649c70f2d0e0fb1df8f9ff8))) (N (L 0xfffffff1af70d16baa2912cb4cc1e3) (N (L 0x1000000090be1deca0fcda94286c19d) (L 0xfffffffa5f401b27698633cfd8191a)))) (N (N (L 0x10000000372b58ae0c527a32aee45d6) (N (L 0xfffffffdeb2fe5d496b545d0f7edbf) (L 0x1000000013cf91b7b14e9d15a64f9a7))) (N (L 0xffffffff4615a75ac24e940fa54f96) (N (L 0x1000000006b8c3b7a1aa80521465f00) (L 0xffffffffc29eea425d2df5ec7d117c))))))) (N (N (N (N (N (L 0x100000000229223cc0e2945a1e88225) (N (L 0xffffffffecc731a13eec3f9f640fc5) (L 0x1000000000a8dbcc677f32f31f73d7e))) (N (L 0xfffffffffa46d3b2152a8a99617941) (N (L 0x100000000031107ff0755b9672d7178) (L 0xfffffffffe605527ebfdc54f810926)))) (N (N (L 0x10000000000d98e3e722439ed84de2e) (N (L 0xffffffffff8f6b8f8c7c84b1408d2d) (L 0x10000000000399cafb573043a578aff))) (N (L 0xffffffffffe2d6745edb02c9bc24de) (N (L 0x100000000000e9aa65a2d1d59ab69ff) (L 0xfffffffffff8c352fd3807cc12d974))))) (N (N (N (L 0x10000000000038ca78cce458de14175) (N (L 0xfffffffffffe46d7cc2d2796d13ac2) (L 0x1000000000000d40f90445549f5e0f2))) (N (L 0xffffffffffff9b0ea52e983b42ada3) (N (L 0x10000000000002f96e5174e33b60723) (L 0xffffffffffffe9c6790d5e49dd1287)))) (N (N (L 0x10000000000000a48735552de4af1d4) (N (L 0xfffffffffffffb491ba9aabdb06019) (L 0x100000000000002245bb75c0d98a7a4))) (N (L 0xffffffffffffff090ca90c4e0ef736) (N (L 0x1000000000000006e3f1ead5580e472) (L 0xffffffffffffffcf341fdcec7dfb12)))))) (N (N (N (N (L 0x100000000000000156a71bc6260605c) (N (L 0xfffffffffffffff6add71efe757d70) (L 0x10000000000000004060bcd41fbe269))) (N (L 0xfffffffffffffffe46f0b7045ad6cf) (N (L 0x10000000000000000bb5b9c9fcaa7ad) (L 0xffffffffffffffffb10937a0b98e56)))) (N (N (L 0x100000000000000002105e348dd97e1) (N (L 0xfffffffffffffffff24b8253bf1d35) (L 0x1000000000000000005a52047a4cd95))) (N (L 0xfffffffffffffffffdb12d9eba9258) (N (L 0x1000000000000000000efc8062d8274) (L 0xffffffffffffffffff9f63ba8f3aec))))) (N (N (N (L 0x100000000000000000026a5cc1ec3c4) (N (L 0xfffffffffffffffffff0a601546a42) (L 0x1000000000000000000060e34d51447))) (N (L 0xfffffffffffffffffffda0b6c3f565) (N (L 0x100000000000000000000ec4984bb7c) (L 0xffffffffffffffffffffa4ae13d6fb)))) (N (N (L 0x100000000000000000000230f3b8d0e) (N (L 0xfffffffffffffffffffff2a0c9c42b) (L 0x100000000000000000000051130a006))) (N (L 0xfffffffffffffffffffffe179619d4) (N (L 0x10000000000000000000000b6bbcea7) (L 0xffffffffffffffffffffffbc0f4f49)))))))

private def cneg_lf_108 : FastDTree := dleaf cneg_bt_108 0xfffffffffff9568f93f5be629eb4e9 0x1000000000004b643039e91242c359a 0x1000000000000b3af4cb34b0c4eb9ac 0xffffffffffffa255a1047c07ffe65b 0x828eb6118793a976155 0xcaa233b4b711cdee49 (M 0xfffffffffffa038ff9880624f02a4d 0x10000000000030165d89335b913382b 0x1000000000000989c7611df032156cd 0xffffffffffffc389914a52a0df7f76 0xfffffffffff4428d0fd66e223d2151 0x1000000000017a7e7ea54fd40061f24 0x100000000000a77d155d02b716040b6 0x1000000000036e7fc0ff42ef577460d 0xa42740cf389d1d2b6c (Q 0x6b2be2171377972a3b9 0x1a68ad03926560209d79 0x37e529d94df6da36a68c)) (M 0xfffffffffffb8b2feac49750ebbbd9 0x1000000000000cd17d65b24166d9767 0x1000000000000649b5ab2127b2af961 0xffffffffffffef8b785783fef86751 0xfffffffffff3ea3a012b9ba815f1bf 0x100000000000c6c33f40b3ed23c3044 0xfffffffffffab06781c4c969bbeb68 0x10000000000238a2eae136c8fdcf7c8 0x65f1ddf95314bcea94 (Q 0x4871a5cc4e7c19f9f05 0x1154cb25eb5db5c75f5d 0x23ef3574c65fe12d0408)) (M 0xfffffffffffcef53c1617abeae636c 0xffffffffffffb8411bc2a5438efdf7 0x1000000000000381b85428c3adbe9f1 0x1000000000000057c58abf997f78bb7 0xfffffffffff60921af3ff533b35e73 0x10000000000057f58574915440aa696 0xfffffffffff592b9d29dd6250ac8d6 0x1000000000014b7954b28f80085a241 0x38604878d17fcd5b97 (Q 0x313f2725590c0b36eb1 0xb6157604624fa9cc487 0x17316d34d40196d9eeee)) (M 0xfffffffffffe036118a9e5317794c6 0xffffffffffff4c75f3b382f8cd5bc1 0x1000000000000154b50b1dbebbb065f 0x10000000000000d63c89dc47e3eecca 0xfffffffffff8b58b943153e614bc23 0x1000000000001a6f71412ba2451162d 0xfffffffffff5916bb72130d73f07e1 0x100000000000acc31fabf2d63f3d079 0x1927cbe2b8f089e57f (Q 0x21b6143cdc48608c513 0x779c7ea2cb614341cc0 0xf03898fbea8fc6f4492))

private def cneg_bt_110 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff496519efc09b24d9e022f) (L 0x10000000045a04e6c5a386ff18aa1ad))) (N (L 0xfffffffed4e270cece8f9cd7b9cf60) (N (L 0x100000003f218b206683a99a056dd38) (L 0xfffffff4e3fba0e13b91a4fd2283b9)))) (N (N (L 0x10000001b0cda3b63021c89b9183599) (N (L 0xffffffc59d1c3ad0060428960dc8a1) (L 0x100000071b9b94a53650322ff13f594))) (N (L 0xffffff356643f304ed65d1157ce851) (N (L 0x10000014d93c3f506503c5a749c0c8f) (L 0xfffffe0023d4b55e88099c7be4c045))))) (N (N (N (L 0x1000002e0ff2499a0dd87ccc367f6ac) (N (L 0xfffffc169e8e8acd9c0fdcfa1f0894) (L 0x10000050a1c3b313ea466e8240065c4))) (N (L 0xfffff9d195dfb14bd123bf2a4f217c) (N (L 0x10000073e6cce32de32737ef76beaea) (L 0xfffff7dd4c21297b1c61fc7affc5b6)))) (N (N (L 0x1000008c7bd920d4c2ddab178f98986) (N (L 0xfffff6df4bcac0e1303a9e6549ac01) (L 0x100000928e6e6b3ad2d9ca1a12a453f))) (N (L 0xfffff71c2d709cb9355c37af75df34) (N (L 0x10000085be4cfb9d51a18bb835b0534) (L 0xfffff85fa0115770bb1b3df6afa200)))))) (N (N (N (N (L 0x1000006c2e17ddd5b575284f1b7cc8a) (N (L 0xfffffa2af9de262dc52a872f3e0283) (L 0x1000004e68548cec529cf5228a566df))) (N (L 0xfffffbfc0b17774b21e75965418849) (N (L 0x1000003363c0b173bb7e6aa84b9139f) (L 0xfffffd7d646f98280011d9a44a27f6)))) (N (N (L 0x1000001eb22c5535dfb4196bc6249f9) (N (L 0xfffffe909f475333d914aa2c11ce93) (L 0x10000010d284e50867211c71bf83ab6))) (N (L 0xffffff3eb847e8504b9ab88a2f2d7c) (N (L 0x10000008820494deb8b266b228dfa87) (L 0xffffffa1e94c26301d23cf94de95a1))))) (N (N (N (L 0x10000003fdc1a5c1b62c130ff842c56) (N (L 0xffffffd56a6d1a17c14a556912212a) (L 0x10000001bea117a67dece9234989622))) (N (L 0xffffffee010d8f359846b1fa217f13) (N (L 0x10000000b6a524ad4f40f27b467e1ec) (L 0xfffffff8df41e9fdc95de63b7de7c7)))) (N (N (L 0x100000004620e4c2ca4f165c384e919) (N (L 0xfffffffd584475c365f032a3b6c7b1) (L 0x10000000195d26bee2d74fe38eb5006))) (N (L 0xffffffff112131db52e3fad695c865) (N (L 0x1000000008aaa30af17fed4ba88c94a) (L 0xffffffffb096643be132fc3847951c))))))) (N (N (N (N (N (L 0x1000000002ce19f01d931f20edccd85) (N (L 0xffffffffe6f5e3aebf0ba9142b41fc) (L 0x1000000000dcb47bb0b5c7b1ce7c241))) (N (L 0xfffffffff87e9251c65e6d3be67c69) (N (L 0x1000000000408e497f16f0021ef463c) (L 0xfffffffffddb4cecbeac3133db72e0)))) (N (N (L 0x10000000001201d997a88340b154f4d) (N (L 0xffffffffff6a6d59fc32f9adaac4bd) (L 0x100000000004cc98bb67f6f1e0e087d))) (N (L 0xffffffffffd9022dc3f6c7ed662342) (N (L 0x10000000000139675750e0039b31b77) (L 0xfffffffffff6435d526c1ca4e457ad))))) (N (N (N (L 0x1000000000004ca4d51ebad5c347b91) (N (L 0xfffffffffffdaacc76f6bc960195a1) (L 0x10000000000011ff16a1de1de5aae90))) (N (L 0xffffffffffff7685e164333fc51161) (N (L 0x10000000000004101f31d9b6100ca41) (L 0xffffffffffffe18cf1cf0fbb3675ed)))) (N (N (L 0x10000000000000e214a0a7e561a1194) (N (L 0xfffffffffffff980bb615a6a930ff6) (L 0x100000000000002f5ea13ef6567f6ac))) (N (L 0xfffffffffffffea9b0c96d0bf82e58) (N (L 0x10000000000000099419fd6989cf1ad) (L 0xffffffffffffffbbf9408df5111aa1)))))) (N (N (N (N (L 0x1000000000000001df0a3612f713db2) (N (L 0xfffffffffffffff2eeafe396e2db48) (L 0x10000000000000005a81fc9647f434a))) (N (L 0xfffffffffffffffd923339aaa03eab) (N (L 0x1000000000000000108dcfd1c34a0eb) (L 0xffffffffffffffff901081faa95721)))) (N (N (L 0x100000000000000002ef078beb773fb) (N (L 0xffffffffffffffffec777a6a7aee1b) (L 0x1000000000000000008113a83910698))) (N (L 0xfffffffffffffffffcb165db1858a4) (N (L 0x1000000000000000001588089b78c94) (L 0xffffffffffffffffff74d45483476a))))) (N (N (N (L 0x100000000000000000037d1d20ae265) (N (L 0xffffffffffffffffffe9c4fc9445d8) (L 0x100000000000000000008caaf4450e2))) (N (L 0xfffffffffffffffffffc8c068e1d21) (N (L 0x10000000000000000000158d3c7f9ba) (L 0xffffffffffffffffffff7a640a8350)))) (N (N (L 0x100000000000000000000336cf35c55) (N (L 0xffffffffffffffffffffec5619df11) (L 0x100000000000000000000077857b798))) (N (L 0xfffffffffffffffffffffd2e2b3284) (N (L 0x100000000000000000000010ebc7df8) (L 0xffffffffffffffffffffff9b17528f)))))))

private def cneg_lf_110 : FastDTree := dleaf cneg_bt_110 0xfffffffffff949d70e4cd564b73758 0x10000000000049c45936eae6979671b 0x1000000000000ad8245f6054a1cc7d9 0xffffffffffffb0d9ca14c6179a1046 0x8247e1adc6bdc85e498 0xbeb5d83f266ce021a3 (M 0xfffffffffff9fba55ed6110176b08f 0x1000000000002eb622f18dd14edc118 0x100000000000092966aa4b5f411cb8e 0xffffffffffffd0e7e0a5f0775e8997 0xfffffffffff3ff5a1759ba64014f3d 0x10000000000176863e78db08421f954 0x1000000000009e4c8c99197ccdcf159 0x1000000000036df15aa5b37406fe4bc 0x99f7d1c6323f4ba8d2 (Q 0x6b018e7da976efe45a0 0x1a4e3c3b9c26ce8e9b94 0x37c1993a4aef518d5464)) (M 0xfffffffffffb899ca4e9b9f39994a6 0x1000000000000beb37189759c1c2597 0x10000000000005f12768ef3ecc71ef6 0xfffffffffffffb08a33b5e8abdbb2e 0xfffffffffff3c618934d5a1fbe22a0 0x100000000000c32f0643a7ce0f77799 0xfffffffffffa4a2a86b8ea4b47eac5 0x100000000002364f18ab51aa08b49b5 0x5f33e8bc4d10e0fae7 (Q 0x4863267b33230c0c02b 0x11456e8ca2a7bdebc5fb 0x23da1bc947d002694f67)) (M 0xfffffffffffcf0e119059e7beed2cc 0xffffffffffffb05ead4ca1f9dfb471 0x1000000000000332fb8d4388255b029 0x10000000000000f942958b45b19518e 0xfffffffffff5f9a5676e51bd5914c3 0x100000000000550df3582636620cec9 0xfffffffffff5524fb39d8afc170a75 0x100000000001488f5ad6a73d72c332b 0x35818004c27fabd0a2 (Q 0x31328eecad71fb30ac7 0xb58d98c02bc84cdc58a 0x1725424eb44f3f5a25f4)) (M 0xfffffffffffe06054c35015236ae8c 0xffffffffffff49a7e4550e906f7ffa 0x100000000000011025991c588ce5831 0x1000000000000167a5f7f07a8e733da 0xfffffffffff8b26c454844724b4d1a 0x10000000000018415e32e13a20a467c 0xfffffffffff56d50342929b33a48ec 0x100000000000a9f6288ae08e5e8688b 0x1c308647e921dfdfcc (Q 0x219d598a96acfebc65c 0x7756ec464ea24383b1a 0xefcd2ebee6cb1148609))

private def cneg_bt_112 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff4709ea5fda36beed33f53) (L 0x100000000475155d1e3f6cb5b2da0f8))) (N (L 0xfffffffeca81c7540939a0a5acbe46) (N (L 0x1000000041ee7e9c4584274eddef258) (L 0xfffffff44bf40d3b67328b2325e0cd)))) (N (N (L 0x10000001cbac81c260d5229bb4e222c) (N (L 0xffffffc181f5ccda8fe23f5ca78d4f) (L 0x10000007a9f7493a897ef6438708dc6))) (N (L 0xffffff24011a779f3418a7c4faa3b2) (N (L 0x10000016cad668516825a0cfffa3dfd) (L 0xfffffdccc216efa5a1cd6049f0ea69))))) (N (N (N (L 0x10000033019f3015708d0e084ee2df5) (N (L 0xfffffba45b1dfd1fa5d13ba1454299) (L 0x1000005a5d89d82ccd7b7a3054cb090))) (N (L 0xfffff9085729fd9ad7bc429c338deb) (N (L 0x100000835fdc5559c95105ba7c8fccb) (L 0xfffff6ba5885fce9a219d91f8b5648)))) (N (N (L 0x100000a0f6b6904ad796ac4cc64b822) (N (L 0xfffff57caff018770944e388c2f19c) (L 0x100000a9a873a3ad0e138aef4bd353f))) (N (L 0xfffff5a8496f32828c0f4d9de4b393) (N (L 0x1000009c5c052dbd164f498b99c404e) (L 0xfffff70a871c6a6c212465cd44891b)))))) (N (N (N (N (L 0x1000007fada796501b2b3fde8f4d248) (N (L 0xfffff915ba654306b9807b543a6ad5) (L 0x1000005d63cb1304c6f333429469a03))) (N (L 0xfffffb32267008e0d6668f2526de68) (N (L 0x1000003dc0bd80e7af51b09c386f016) (L 0xfffffcf876cdba6d5c7691cf0590c6)))) (N (N (L 0x100000253417a2432899535eee4532e) (N (L 0xfffffe40debe4fdc2ee1156ff39cf7) (L 0x100000148f145d2c34cf7b23e35be11))) (N (L 0xffffff12d33cb7a545cee5bf04672f) (N (L 0x1000000a7b687da00c09249d0f2fb34) (L 0xffffff8b9e5bdbf74b7b1abe7d8f65))))) (N (N (N (L 0x10000004f4cc4779636098bdae361ca) (N (L 0xffffffcaea3c898c4a7b0e58fcf3f3) (L 0x100000022ee41029f23b5c59c9a1a32))) (N (L 0xffffffe9654e88de9c89efcac17332) (N (L 0x10000000e645f78fc3a30b11c703035) (L 0xfffffff6faee0130c60648bcd08d83)))) (N (N (L 0x100000005910e946658316a16f2cc63) (N (L 0xfffffffc9d9862d56e2637c1780259) (L 0x100000002071e5efacc51ed5d02413e))) (N (L 0xfffffffecd5cc18680404ccc05d2a5) (N (L 0x100000000b2a068bb0267c16c87b3ee) (L 0xffffffff9958e8f868adea2e3846c1))))))) (N (N (N (N (N (L 0x1000000003a37003b914b3660bf9a47) (N (L 0xffffffffdf69500910b9ed744f2758) (L 0x100000000120361f895e4dfc20fba3e))) (N (L 0xfffffffff62a81d44f5e5bd7faac9a) (N (L 0x100000000054dc92994c3e6df4555ec) (L 0xfffffffffd2c5921abbb66e0e92745)))) (N (N (L 0x100000000017d36badd6a9cf49553a8) (N (L 0xffffffffff3975a11da6766a70324e) (L 0x1000000000066404fba46afc31eed72))) (N (L 0xffffffffffcbea01eedc121f945495) (N (L 0x100000000001a3f76579f438025748f) (L 0xfffffffffff2e96ede61dd335a378f))))) (N (N (N (L 0x10000000000067577610dbb302a26d2) (N (L 0xfffffffffffcd84e76478ac51c1c55) (L 0x1000000000001869db85d491ad06a40))) (N (L 0xffffffffffff44f094b070a3b4de97) (N (L 0x100000000000058b7e75d03ea83e4a3) (L 0xffffffffffffd6522e8e2630ca07ac)))) (N (N (L 0x10000000000001365ece77426db0560) (N (L 0xfffffffffffff70ded73b0db31501c) (L 0x1000000000000041691df9aa1c2e6b4))) (N (L 0xfffffffffffffe25f490a4d26c4612) (N (L 0x100000000000000d4d837f7168a8408) (L 0xffffffffffffffa14140c341b5607e)))))) (N (N (N (N (L 0x10000000000000029d149d44bb6a8d1) (N (L 0xffffffffffffffedb26dbf1deb3e72) (L 0x10000000000000007f1f63692f1910a))) (N (L 0xfffffffffffffffc943a5d6935f4b2) (N (L 0x10000000000000001761307e2997ff9) (L 0xffffffffffffffff617a177a6c5e18)))) (N (N (L 0x1000000000000000042a81190a0d0ea) (N (L 0xffffffffffffffffe42fc1e9d513ca) (L 0x100000000000000000b8496fe15fe05))) (N (L 0xfffffffffffffffffb440c47a68162) (N (L 0x1000000000000000001ee7b88f9f3bf) (L 0xffffffffffffffffff37b683593c56))))) (N (N (N (L 0x1000000000000000000508b34fc7d15) (N (L 0xffffffffffffffffffdfd6cfaa8a63) (L 0x10000000000000000000cc0867b6bfd))) (N (L 0xfffffffffffffffffffafa84cb715d) (N (L 0x100000000000000000001f6bd123718) (L 0xffffffffffffffffffff3cb5214ae8)))) (N (N (L 0x1000000000000000000004b5bb6e3fd) (N (L 0xffffffffffffffffffffe31cc07cfe) (L 0x1000000000000000000000b0077e275))) (N (L 0xfffffffffffffffffffffbd63d074d) (N (L 0x1000000000000000000000190ba8fea) (L 0xffffffffffffffffffffff6a4539dd)))))))

private def cneg_lf_112 : FastDTree := dleaf cneg_bt_112 0xfffffffffff93f3b2f1fe1b68d14aa 0x100000000000483185be42d35275b8e 0x1000000000000a8a3042a1f434ea276 0xffffffffffffbefe937eaa812f9110 0x81f276388768cdcd57d 0xb4bbbcd13d89cbf29b (M 0xfffffffffff9f5ad1ccf93243effa7 0x1000000000002d629065f1221881fc2 0x10000000000008dddd732a8c03ffef6 0xffffffffffffddf3d6e2465f833c97 0xfffffffffff3bea0f7c94d0ffaf397 0x10000000000172951c6a992c55cf00e 0x10000000000095462752b5d7ea5e253 0x1000000000036d4ee045276e53138ee 0x91e56cb45a4bbfeda2 (Q 0x6ac5766d1469af66632 0x1a3433279cb9a589a925 0x379eac4c72ec05411f85)) (M 0xfffffffffffb89b6863f53c35466fc 0x1000000000000b107521e51752c2dad 0x10000000000005ad45b938963e93a59 0x10000000000000649c79cb9fb71910f 0xfffffffffff3a3d49a5aaa828f1f27 0x100000000000bfa5727fb2caad4e9e8 0xfffffffffff9e62b0f103af313b0b8 0x10000000000233f274fcf05f970e0f8 0x5b0c47ed4ccdddf839 (Q 0x483eca8731c5ddf5b97 0x11362e271bd56f5496c3 0x23c553bc36101e095f23)) (M 0xfffffffffffcf3e84bad6ea06f77b9 0xffffffffffffa91db83f76b9d1c3a5 0x10000000000002f8a280db37e8fde0c 0x10000000000001981c93a6fbc935f65 0xfffffffffff5eb8513176ce95e15b2 0x100000000000523237d20a94b7b7178 0xfffffffffff513b3d152f0e12bdd2c 0x10000000000145a4170c2b752a6ef80 0x35f398643d7f2f61cd (Q 0x310eacba80e7f9e4da7 0xb504954650527115aca 0x171935e98007f5572126)) (M 0xfffffffffffe09fe83ae88ec931561 0xffffffffffff4763bd66bfd4b38e36 0x10000000000000dfa09ea08bf67ea09 0x10000000000001f74be1c25b2bdd171 0xfffffffffff8b042e8ff5773d74594 0x100000000000161ed55949a48224921 0xfffffffffff54a981f873597f92b39 0x100000000000a72c6f1d7b49120c5f2 0x226c32c91849613b3f (Q 0x216e0370a0935300133 0x770e86e5e98263c7db9 0xef61c5e56cadd2563d7))

private def cneg_bt_114 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff44aebacff3d2590087c76) (L 0x1000000004907ea708672ab390a82bd))) (N (L 0xfffffffebfe0f065d897878dab471d) (N (L 0x1000000044d43127529c933934d7222) (L 0xfffffff3ad36293d1a8e4ed4c9b7d6)))) (N (N (L 0x10000001e7f972ca9f43720d5c4d752) (N (L 0xffffffbd25d3416da6c8f32bfc6933) (L 0x10000008424b9a3ade57f5f75a8a540))) (N (L 0xffffff1140e35ddf63745ec24ca609) (N (L 0x10000018e7015549af3c8113d56b070) (L 0xfffffd949a61b1d5c9ca16bf86e104))))) (N (N (N (L 0x1000003871e8c408e8d67418cc0e35d) (N (L 0xfffffb25de8c022b54d6083413a3fa) (L 0x1000006534b5ec0a88a662fa9963dae))) (N (L 0xfffff826e122315c5f417cddfd55dd) (N (L 0x10000094cf1c314e5dc0ecb884ba429) (L 0xfffff570ab765b0d6d2651565fa54a)))) (N (N (L 0x100000b84bd49754bc2c53dc3e7c9ad) (N (L 0xfffff3e6887a2d56579d99e37ba9e5) (L 0x100000c44167cd23739aa8fb0b02c95))) (N (L 0xfffff3f9f05e4e81e2bdf52a020dd3) (N (L 0x100000b6a93cea970efa511428215d9) (L 0xfffff57be7f3cae059e59cfc13df1e)))))) (N (N (N (N (L 0x1000009692f903bd18bf969e3ddb7b4) (N (L 0xfffff7cea3c76df3128e3fe3ac753d) (L 0x1000006f25a6e724c3548e12d4b7f82))) (N (L 0xfffffa41c6d1eef8a2ace9dfc31091) (N (L 0x1000004a257a4b21743c063e29601c4) (L 0xfffffc58cbb1e3d4009bec2ea9639a)))) (N (N (L 0x1000002d0dc7aaab731a0a302e823de) (N (L 0xfffffde04059bde480a2565cba8b58) (L 0x100000191acd10550d4cc08f955db9a))) (N (L 0xfffffedd3418073076c7bca28d0bbd) (N (L 0x1000000ce74edb57e4c089b345d8d27) (L 0xffffff702a375a0d9b36330f97e2ee))))) (N (N (N (L 0x10000006263d221844645113109a0d6) (N (L 0xffffffbde18e0a14ed2caa027adff2) (L 0x10000002bac5eb6ce1abf5bb2f195be))) (N (L 0xffffffe3a1ae82ac153c3c2c93f09d) (N (L 0x1000000122124ecc327732d4c5d8e9e) (L 0xfffffff49893d354ccd24c74cae33d)))) (N (N (L 0x100000007104f155a4e74ca1c196350) (N (L 0xfffffffbb09f0032b45c83a6c5edeb) (L 0x1000000029776c55e27fc9a2925987e))) (N (L 0xfffffffe76b72170a0269d361bf74c) (N (L 0x100000000e5e6eb1c05fe4eab21d59a) (L 0xffffffff7b6c5f9da6e39bee522887))))))) (N (N (N (N (N (L 0x1000000004b7145a601eeb53f57e4b6) (N (L 0xffffffffd59fc2d5730c90e5de95b9) (L 0x1000000001780783e4e6b1a68c0b5bb))) (N (L 0xfffffffff3207d6a2fb7fd7a0d545e) (N (L 0x10000000006f7446072e245b2b3e701) (L 0xfffffffffc4679338754977d7f1e65)))) (N (N (L 0x10000000001f7f030496902f6d3b3e7) (N (L 0xfffffffffef8b32026a97da1793930) (L 0x10000000000880919796ef1896bb276))) (N (L 0xffffffffffba7c5471af1c55483a38) (N (L 0x100000000002323f6a58a23d27fb564) (L 0xffffffffffee6c577216530cb0b9ea))))) (N (N (N (L 0x1000000000008b360e385aac145cb28) (N (L 0xfffffffffffbbca12123593e4b2549) (L 0x100000000000211691a0012f4773c5b))) (N (L 0xffffffffffff01b588f7d9c2998fec) (N (L 0x100000000000078f70f771d14342d92) (L 0xffffffffffffc700cc477052cafcd0)))) (N (N (L 0x10000000000001a9b06b2d3edcc48d6) (N (L 0xfffffffffffff3b1da73fa6cbd2b34) (L 0x100000000000005a3cf5a25a24a4272))) (N (L 0xfffffffffffffd702342aed5fe828b) (N (L 0x1000000000000012752fdf713086b18) (L 0xffffffffffffff7c2a781845e94a21)))))) (N (N (N (N (L 0x1000000000000003a5a1d2ec9c1422c) (N (L 0xffffffffffffffe66367e150ca699a) (L 0x1000000000000000b26194c4c45d5eb))) (N (L 0xfffffffffffffffb2fb09d93a5ae4d) (N (L 0x100000000000000020fd0b8d6801f18) (L 0xffffffffffffffff1fb682101ddab0)))) (N (N (L 0x100000000000000005e90e166e64483) (N (L 0xffffffffffffffffd86f26b4d12322) (L 0x10000000000000000106dc5cecdd4b5))) (N (L 0xfffffffffffffffff93ab0cfae7439) (N (L 0x1000000000000000002c513f9961b4a) (L 0xfffffffffffffffffee008a0e064dd))))) (N (N (N (L 0x1000000000000000000741b7eda2906) (N (L 0xffffffffffffffffffd18480243d58) (L 0x1000000000000000000127a7fe2ec35))) (N (L 0xfffffffffffffffffff8b4728ed63a) (N (L 0x100000000000000000002dc41a90d9a) (L 0xfffffffffffffffffffee2d2b2e89f)))) (N (N (L 0x1000000000000000000006e52690881) (N (L 0xffffffffffffffffffffd59a4000f7) (L 0x10000000000000000000010300641f2))) (N (L 0xfffffffffffffffffffff9dbf707a5) (N (L 0x10000000000000000000002508f2bf3) (L 0xffffffffffffffffffffff220bd52f)))))))

private def cneg_lf_114 : FastDTree := dleaf cneg_bt_114 0xfffffffffff936ab5df86370a2f89c 0x10000000000046a8a87f631e34cc8d1 0x1000000000000a50c2ca1d2bae3af42 0xffffffffffffcca14c9e521e425a53 0x818c8cff92894cc507b 0xacdbb8bcf794df0f4a (M 0xfffffffffff9f198773daa79b41280 0x1000000000002c18994b31bc59271e2 0x10000000000008a6d607cb44f7558c8 0xffffffffffffea89fe118b0c5b52f6 0xfffffffffff380456589079f8a0a97 0x1000000000016eaafe616381d37756c 0x1000000000008c687342f901cd500b1 0x1000000000036c992dd31a098097ad7 0x8c15035fed2d82431d (Q 0x6a764217fc7d3cec9b6 0x1a1a8977532911f24128 0x377c5a4f6880e271aee2)) (M 0xfffffffffffb8b7202c617e199723c 0x1000000000000a3e31232dd2ee5ad3b 0x100000000000057dbbfda597cb97684 0x1000000000000112a1e42b90f13da07 0xfffffffffff38357428ac4621ecd4a 0x100000000000bc263db7ecd6d4bdd19 0xfffffffffff9845492e6f838d2e126 0x100000000002318d88b5808a4867336 0x598540e860e71bc824 (Q 0x48045259357b924ebfd 0x11270618c48f9c4bf747 0x23b0d8ebf2158c5092be)) (M 0xfffffffffffcf860597e8b0cacb9d8 0xffffffffffffa24e7fcf30c525cbf8 0x10000000000002d25aa9eec90e5d316 0x1000000000000231f6462862e752aed 0xfffffffffff5deaea4f98469f49b1c 0x1000000000004f61f29afa521cd58e6 0xfffffffffff4d6d484520a2e4f2d93 0x10000000000142b7d40379b839151c8 0x393399f4c16c6cfd28 (Q 0x30d43602dc51d929fc7 0xb47a60505c0fac5665b 0x170d469dca1f96e34427)) (M 0xfffffffffffe0f45be24b29718650c 0xffffffffffff457a914da24e93ffb4 0x10000000000000c2d6353290afc6700 0x1000000000000282c3f43859cc28ab4 0xfffffffffff8af017f5a8a70834d6e 0x100000000000140769a391cebe5ac87 0xfffffffffff52934b1f54cc0dced74 0x100000000000a46611b00ff4c941fac 0x29faa721e7957a9f0b (Q 0x2129803033951cdd023 0x76c366fd70a3dd15d9e 0xeef666ed35a9fdbeec6))

private def cneg_sub_12 : FastDTree := (dsplit (dsplit (dsplit cneg_lf_100 cneg_lf_102) (dsplit cneg_lf_104 cneg_lf_106)) (dsplit (dsplit cneg_lf_108 cneg_lf_110) (dsplit cneg_lf_112 cneg_lf_114)))

private def cneg_node_13 : FastDTree := dsplit cneg_sub_11 cneg_sub_12

private def cneg_bt_118 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff42538b400d6df313db999) (L 0x1000000004ac40c4841ac0f8b2146f5))) (N (L 0xfffffffeb4ff1ab9640f133b40291e) (N (L 0x1000000047d33aef1a2d4aedbf398d2) (L 0xfffffff30786f35da31b5fac8e9f63)))) (N (N (L 0x1000000205c48cbaccee455bde9fb0b) (N (L 0xffffffb8854335cad837f071dd9d1c) (L 0x10000008e535ac7d04f7dc8a48e3ba6))) (N (L 0xfffffefd0d68a95a7143e2578a08cd) (N (L 0x1000001b310afce9a7c177face79788) (L 0xfffffd574490a87e0af54d40539bad))))) (N (N (N (L 0x1000003e6c875f7f545bb413420caf3) (N (L 0xfffffa99f0e77fad504099442e1a45) (L 0x10000071457ed945150ce3e0b301763))) (N (L 0xfffff72a75025cc37f43432b019def) (N (L 0x100000a870c93aa079df93f2fdca4fe) (L 0xfffff3fb5ffed8798b771fe19b6e74)))) (N (N (L 0x100000d2dc197938035c7a7a165545f) (N (L 0xfffff215ace688feebb70434fdad3e) (L 0x100000e2db0060148afd11a8100ad02))) (N (L 0xfffff208501b28398d8033576b55ed) (N (L 0x100000d539d919c027a8dc7e7242949) (L 0xfffff3aa695f52ece56e81ed3f195a)))))) (N (N (N (N (L 0x100000b17054fd785f1ad5304f6c317) (N (L 0xfffff64d0cb03abf925dc4d9280869) (L 0x100000842d47a3d2ccf26a4d13c7798))) (N (L 0xfffff923d05b0ce8c094817ada6e7e) (N (L 0x10000058f4c6f1f7898a71046dbf6f3) (L 0xfffffb99295ae16820a587a0253bbf)))) (N (N (L 0x100000368438047ac60576437ff105c) (N (L 0xfffffd6b4b433b65c27906861bc7a8) (L 0x1000001ea163f22caad7b4bd1416706))) (N (L 0xfffffe9bc0da8c01488d60027b0418) (N (L 0x1000000fdf0871629b5ed74f4955f7e) (L 0xffffff4e6235d8564952acd30c2d49))))) (N (N (N (L 0x100000079f915e3aa3cacceb219defa) (N (L 0xffffffadb76de6bcc8032313e635bb) (L 0x1000000368ec974d26335ab118be576))) (N (L 0xffffffdc6d8ac73681df548e9d8867) (N (L 0x100000016d15cfe928a17f0fa70ee8a) (L 0xfffffff19811b1092893a7d97357b2)))) (N (N (L 0x100000008f4a5f5e7f5f2c17e650b24) (N (L 0xfffffffa840d02f620495b93ddddeb) (L 0x1000000034f34eb271c81af075405d5))) (N (L 0xfffffffe080696173de15d17da0bcf) (N (L 0x10000000127a2ecd3c9dc1840eedd23) (L 0xffffffff54ed5db72f24df1bfe7acd))))))) (N (N (N (N (N (L 0x10000000061ae8c858bbbbb43610bfc) (N (L 0xffffffffc8f23c74ccca2da9dbf8e1) (L 0x1000000001ea2b2ce02df14e75800a4))) (N (L 0xffffffffef29e21b397b50a0e6bdc0) (N (L 0x1000000000923fb224fbbf061ef05d4) (L 0xfffffffffb18b4a8c87ca5e319b880)))) (N (N (L 0x1000000000299923a9ae64537048ece) (N (L 0xfffffffffea321d4e9d08079fbbaeb) (L 0x10000000000b4d1832f5862a4327fba))) (N (L 0xffffffffffa34f4f59851699db8e6c) (N (L 0x100000000002f00c16ed69fde531e5e) (L 0xffffffffffe86aae9cbd56e42c64f6))))) (N (N (N (L 0x100000000000bb5bf313dab6e9af195) (N (L 0xfffffffffffa3eac3a06712966fea0) (L 0x1000000000002ccdc9f3dd51c6cc70b))) (N (L 0xfffffffffffea6a24e336eab1d0677) (N (L 0x1000000000000a4c7bb92eb55508dd4) (L 0xffffffffffffb220b280570d3ef389)))) (N (N (L 0x1000000000000247502bb85e96e9d11) (N (L 0xffffffffffffef16cb0525bcd41956) (L 0x100000000000007c5f8f3e9a77dd35c))) (N (L 0xfffffffffffffc756e928e232eee05) (N (L 0x1000000000000019961db01c06bfb62) (L 0xffffffffffffff48badae2874d1a17)))))) (N (N (N (N (L 0x100000000000000515903076d9a31f3) (N (L 0xffffffffffffffdc31e1f8043cde4f) (L 0x1000000000000000fa128cc36f68a21))) (N (L 0xfffffffffffffff93ba31c48f92f8d) (N (L 0x10000000000000002e809cc84027407) (L 0xfffffffffffffffec2f78a648af1ef)))) (N (N (L 0x100000000000000008608aecc04907a) (N (L 0xffffffffffffffffc7c4f845471812) (L 0x10000000000000000176944ddf178cc))) (N (L 0xfffffffffffffffff6536b2443b010) (N (L 0x1000000000000000003f7d544c9bb13) (L 0xfffffffffffffffffe625df9748d9b))))) (N (N (N (L 0x1000000000000000000a736b5e8d58d) (N (L 0xffffffffffffffffffbce20999a6f1) (L 0x10000000000000000001ac034d534b1))) (N (L 0xfffffffffffffffffff5696b98b674) (N (L 0x1000000000000000000042987de8e89) (L 0xfffffffffffffffffffe5ff857f9c7)))) (N (N (L 0x100000000000000000000a15a041bec) (N (L 0xffffffffffffffffffffc1d5b8af03) (L 0x10000000000000000000017cb6e364a))) (N (L 0xfffffffffffffffffffff6f370db95) (N (L 0x100000000000000000000036b5eadcc) (L 0xfffffffffffffffffffffeb74d9f64)))))))

private def cneg_lf_118 : FastDTree := dleaf cneg_bt_118 0xfffffffffff93011e7d09b7693c568 0x1000000000004526c7ee2af47662fa6 0x1000000000000a2b25765d2467f0781 0xffffffffffffd99f8338af3b30d2ff 0x8114c8de366949f316d 0xa729a8a3b842a5dbaf (M 0xfffffffffff9ef537be3febee30706 0x1000000000002ad544cebb372034e74 0x100000000000088399bf238ed1e8334 0xfffffffffffff68733e8bd1d11192e 0xfffffffffff3442cb5deb6919b3d18 0x1000000000016ac7ca891e116258864 0x10000000000083b214345e87bb11b7f 0x1000000000036bd11761123449c3314 0x888e12d4e878e60a1a (Q 0x6a1325ea12aab4fa3d1 0x1a0137bc51f759ad44b3 0x375a9b71f6c5db89b010)) (M 0xfffffffffffb8ebe29a8d94b230115 0x10000000000009717862b6cddc73bd8 0x1000000000000561d46a113325f2e06 0x10000000000001b8559a898a1298cd0 0xfffffffffff3648b05fe3ada397754 0x100000000000b8b1238863272079065 0xfffffffffff92493c107ef445de4e9 0x1000000000022f20d7d756b4026f962 0x5a68054d31bc149345 (Q 0x47b404a3feee88390e3 0x1117f321615ac1df3352 0x239ca78c923de39bb166)) (M 0xfffffffffffcfe3ab8ae5b06ba4e9c 0xffffffffffff9bc27cc6698c5d9b6e 0x10000000000002bf702b95e9037bdd4 0x10000000000002c47c16f4348cebac1 0xfffffffffff5d311154a0ea86b7551 0x1000000000004c9cc62eebea61011ab 0xfffffffffff49ba1325a4ad8dc4766 0x1000000000013fcad9db11abea4d2d9 0x3e668a22a6110b8c1c (Q 0x308455e5a01772d1f3a 0xb3eef5975b9636c6a1e 0x1701735439ef071a007a)) (M 0xfffffffffffe15ce540610c16d3b35 0xffffffffffff43bea20127b6de48f7 0x10000000000000b91505d107497c59c 0x1000000000000307af4a26a8c91bd44 0xfffffffffff8ae9acf7f8055dc9020 0x10000000000011fab12ff497157a0c3 0xfffffffffff509180a294592b0e1c4 0x100000000000a1a32daa4bb8123a37a 0x31d7a8945603d6cdcb (Q 0x20d19fbeedca9c9dcdb 0x7675aa50525a940179e 0xee8b1c156eed0e757cc))

private def cneg_bt_120 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff3ff85bb027098d272f6bd) (L 0x1000000004c85bb5915a2f85171ed9b))) (N (L 0xfffffffea9db7503d3060559f6237c) (N (L 0x100000004aec360e4ac54240a5dfe36) (L 0xfffffff25aaa013fc930eaf495ac59)))) (N (N (L 0x10000002251e722e92721326e81588c) (N (L 0xffffffb39cadbb7cdcd2f2ff582299) (L 0x10000009935aeeb72ef316647c2ea05))) (N (L 0xfffffee74cf868bcaacc3805e11a38) (N (L 0x1000001dac7c1d556de1b6aad1cf964) (L 0xfffffd145071af5a18c1d36506d10b))))) (N (N (N (L 0x10000044fe321f4120488ff9ee86f6d) (N (L 0xfffff9ff3d7989a644bdbb8469ac0c) (L 0x1000007eb11bf91e84bc9eeac42e8bb))) (N (L 0xfffff61009579e035c3c096988d4d7) (N (L 0x100000be87eea9da7d9437e50b6d10e) (L 0xfffff254fb5b7a6dbc552c1ccebcbe)))) (N (N (L 0x100000f114a1046d6442a8bedf9400d) (N (L 0xfffff00202456e1905a1631468d61d) (L 0x1000010608e8893e1d0a54b7ee1d239))) (N (L 0xffffefc9502c01bff7082daae91cd2) (N (L 0x100000f8b7ff65737de0cb78d610578) (L 0xfffff18b3c0ece5af0b2e968a99974)))))) (N (N (N (N (L 0x100000d0efb9ac121ff6da82b22ca8d) (N (L 0xfffff486d7dd415b1f45ba462a8b60) (L 0x1000009d10208dc8cde2acb658378d9))) (N (L 0xfffff7cfe1b53682a5fff4fb29da5d) (N (L 0x1000006aa3a88bbaa929611836164cc) (L 0xfffffab35858a27ae1df8a04848a15)))) (N (N (L 0x10000041e9d6b9dc670ee3887a7f1b6) (N (L 0xfffffcddd4b8be9fd2ddec8cc4e79f) (L 0x100000255787a0353b2509419682bd2))) (N (L 0xfffffe4bee4908a8e3618364c45e0c) (N (L 0x10000013815ae39c28e071f8b793866) (L 0xffffff24d9cf51a0528aa9199aba2c))))) (N (N (N (L 0x100000097150ec34c4bca32cc081fbc) (N (L 0xffffff99afa91481ff67345d3a0129) (L 0x10000004418e826d57e1a2e7b589aff))) (N (L 0xffffffd36ecf04754286ea173cf185) (N (L 0x10000001cb1b18f19fdccd3eacce219) (L 0xffffffedd14000361b7326eb3f0df5)))) (N (N (L 0x10000000b583668d7304a13db238cf1) (N (L 0xfffffff907256530ecaa0477046a99) (L 0x10000000438e5c26b649906dc8347e8))) (N (L 0xfffffffd7abebcd1e568d98c7abbaa) (N (L 0x1000000017bd55f8abe8c6907ebb706) (L 0xffffffff23725b3586984e3c8d06d6))))))) (N (N (N (N (N (L 0x1000000007e5d9cec4ffdd2dd493666) (N (L 0xffffffffb889e878e18c4ca2fc96f6) (L 0x10000000027e631ec6e9834720ace48))) (N (L 0xffffffffe9ffeacc5bcde07e87c8ec) (N (L 0x1000000000bfbc14373b2f1fd14513e) (L 0xfffffffff98cea20ec7cde5e588a90)))) (N (N (L 0x100000000036e41e581b8726e5e558b) (N (L 0xfffffffffe322c3c2f37c1833318e3) (L 0x10000000000f0207a9ebf620bb6c893))) (N (L 0xffffffffff8484df1f901c9fd0cd3c) (N (L 0x100000000003ed0154fb36ccefd5a88) (L 0xffffffffffe062edf88ae7d7541949))))) (N (N (N (L 0x100000000000fbee0d34e9a9eff552e) (N (L 0xfffffffffff83cdb84b7a3c298c7fb) (L 0x1000000000003c9cba6635c83a9b9e1))) (N (L 0xfffffffffffe2b5eee6f4f270bac24) (N (L 0x1000000000000e04255fd4f70715b51) (L 0xffffffffffff95b46b4aca30af62ec)))) (N (N (L 0x100000000000031e902f49d4109f4e9) (N (L 0xffffffffffffe8c7efef72a0b9a513) (L 0x10000000000000ab430bd8dee61c330))) (N (L 0xfffffffffffffb1c0efb758d6ea0fa) (N (L 0x10000000000000236f64c273df86b7a) (L 0xffffffffffffff0176b6040dae3005)))))) (N (N (N (N (L 0x100000000000000714cb0c44f8ca127) (N (L 0xffffffffffffffcdfdc7e37372e70a) (L 0x10000000000000015e3f4afa6e8bbab))) (N (L 0xfffffffffffffff67ef61c15d33720) (N (L 0x1000000000000000417d99e07921a65) (L 0xfffffffffffffffe404acb2c447b46)))) (N (N (L 0x10000000000000000bdcb6bdc8f587b) (N (L 0xffffffffffffffffb02948b5e074e4) (L 0x1000000000000000021545e736cbb67))) (N (L 0xfffffffffffffffff230c7c6761389) (N (L 0x1000000000000000005ade8bf27f85d) (L 0xfffffffffffffffffdae6d3023975b))))) (N (N (N (L 0x1000000000000000000f095db5144e7) (N (L 0xffffffffffffffffff9f2e46ca5bca) (L 0x100000000000000000026b075fb446d))) (N (L 0xfffffffffffffffffff0a59d5d9db9) (N (L 0x1000000000000000000060d004d8c4f) (L 0xfffffffffffffffffffda1a8a37706)))) (N (N (L 0x100000000000000000000ebc218a33f) (N (L 0xffffffffffffffffffffa4f0383c7b) (L 0x10000000000000000000022f1584577))) (N (L 0xfffffffffffffffffffff2ad9a9059) (N (L 0x100000000000000000000050be8173c) (L 0xfffffffffffffffffffffe19b23dda)))))))

private def cneg_lf_120 : FastDTree := dleaf cneg_bt_120 0xfffffffffff92b541c2fb0891eac57 0x10000000000043a90c52b38a401f804 0x1000000000000a18441394ce978a8a0 0xffffffffffffe5d80fa8f4323010b5 0x808a579cdd545f11998 0xa39f34054d73f4e03c (M 0xfffffffffff9eec52290fe7fd1218c 0x1000000000002995bbf8b81c5c3344c 0x1000000000000873143b28d3ab5ac48 0x100000000000001c9b3939b7c537aed 0xfffffffffff30a3db16e173b4b9517 0x10000000000166eb672eedc7597187b 0x1000000000007b21c24ee46358999d7 0x1000000000036af768fa1a46467c286 0x87348b4a958c62c3f6 (Q 0x699be0dd2061e655bed 0x19e837584fe9c47c7a37 0x373968b1fa93008178c8)) (M 0xfffffffffffb9384ca9504bfda5559 0x10000000000008a779e16f9d06648af 0x10000000000005587b8001398ac6132 0x10000000000002538ab67c9f13ae5f2 0xfffffffffff3475b859a4bb705d31c 0x100000000000b545e14dcdab8f37165 0xfffffffffff8c6d6672387c79e077a 0x1000000000022cace14f97ba991b2df 0x5d4791575375e60617 (Q 0x474ea84cacb0c85c994 0x1108f29648939efdf915 0x2388bc4f808aaf9cd3f0)) (M 0xfffffffffffd05637f64497b2b49f9 0xffffffffffff954d3f06fb0895b4dd 0x10000000000002bed182521cc8f428d 0x100000000000034d742e254eed27a6f 0xfffffffffff5c89c401c9642011d24 0x10000000000049e257c4b4095375bce 0xfffffffffff4620a39b60e73b0b17d 0x1000000000013cdd6dd9570d6db65b4 0x44b73a9111661eecad (Q 0x3020a59cac289a94718 0xb36257d37e5d3e7a951 0x16f5bb34504c9d10651a)) (M 0xfffffffffffe1d8624e856a7a0ccd2 0xffffffffffff4204428a3aa454df69 0x10000000000000c14e2ae5382200340 0x1000000000000383ca451db8e8da69f 0xfffffffffff8af024ae7bf3a186255 0x1000000000000ff845560fe0e1931a2 0xfffffffffff4ea351b0ce062f19f61 0x1000000000009ee3df40d08cea1c899 0x39856b6b8c0bd4c647 (Q 0x20688d850df4ec09012 0x76257419f5b6f08bba2 0xee1ff0afc15546db569))

private def cneg_bt_122 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff3d9d2c2040a5273a833e0) (L 0x1000000004e4cf7a30257658bfc76bb))) (N (L 0xfffffffe9e752dfa4ce21f9557f51d) (N (L 0x100000004e1fbe8cb522034585496aa) (L 0xfffffff1a6617b27e4e4a74b73c2ba)))) (N (N (L 0x10000002461855c8e7ffff358b3e74c) (N (L 0xffffffae685308ed9de241cebe18dc) (L 0x1000000a4d6975dacafa3d0b2066c59))) (N (L 0xfffffecfe450c20aba8e3bcb9730b9) (N (L 0x100000205d1bd2bbf58f9b21a319c19) (L 0xfffffccb453621a3c8fafdcc9cefb5))))) (N (N (N (L 0x1000004c34b2834e6f25f02be1d18a3) (N (L 0xfffff954505641010e401d396f0d14) (L 0x1000008d9c0bb3d7d45205c835e51c8))) (N (L 0xfffff4d4429d79bf422f33e3154534) (N (L 0x100000d75f1eb4c96b220043168ef89) (L 0xfffff0775c182b745891932a1cb4ba)))) (N (N (L 0x1000011370311c33a065a9450e85613) (N (L 0xffffeda25cc66051e96f1248c9b88b) (L 0x1000012e731f9195e3380712330d204))) (N (L 0xffffed3164b2bfe9da799c40d49a5f) (N (L 0x10000121e74b210523d66fbae17c46f) (L 0xffffef11e2790a8c1b4514dca8fbdb)))))) (N (N (N (N (L 0x100000f5d68c9dcd7c7750283b38323) (N (L 0xfffff2703801029c1fcd1d8a09a5e3) (L 0x100000ba7d6a06ed22ca4ab13105e23))) (N (L 0xfffff63c1bd3bc98a2aaa7235c2479) (N (L 0x1000007fbc98ca4c78da8000c5bd5d3) (L 0xfffff99ff4ec0f6c5827323356355e)))) (N (N (L 0x1000004fa10f709b3dd0f7d3b4bc0d2) (N (L 0xfffffc32dd73ef14bf16a54c37e4e1) (L 0x1000002d7cab2dcf3eed4d9d4d6532d))) (N (L 0xfffffdeaa8ba0ccd33bae9a39defd5) (N (L 0x10000017f3a6034e9f375675d7d7de7) (L 0xfffffef1d47263c10a8c7457aa2193))))) (N (N (N (L 0x1000000bafb9e174afd233e2ba85c19) (N (L 0xffffff80e2dee7680a1e82c11f45a7) (L 0x100000054eceb197b1fee585c6be80e))) (N (L 0xffffffc835dcd0f7b9b5587dca64af) (N (L 0x1000000240d982f1fb9c4c22aac3a6f) (L 0xffffffe911fb411dac90499b7b53b3)))) (N (N (L 0x10000000e5bc2c7504fd4165f43549c) (N (L 0xfffffff724d9916de377ef308683d3) (L 0x10000000561db9a8a561478b5a4c61d))) (N (L 0xfffffffcc693378f7c263db544b2e7) (N (L 0x100000001e795c784d60a3c7dbb81a6) (L 0xfffffffee3e72ca7d9ab2646c3c0e8))))))) (N (N (N (N (N (L 0x100000000a3543f01bb1f469e50f4c3) (N (L 0xffffffffa352a878bfdc050562e7f6) (L 0x10000000033eb0c6d1241b66e154af8))) (N (L 0xffffffffe3470161616c10c8574124) (N (L 0x1000000000fb24e516af78beb07d5d2) (L 0xfffffffff7864447ac10b2c302f84d)))) (N (N (L 0x1000000000485df62b15097e34b08df) (N (L 0xfffffffffd9d2fbf55f826aaff9fe8) (L 0x100000000013e9a13ef199d11eb92b2))) (N (L 0xffffffffff5ba5ec4f2dfe2a2e299a) (N (L 0x1000000000053dd5873d6d67f937047) (L 0xffffffffffd5a9021a139c67a0f1a3))))) (N (N (N (L 0x10000000000152723de3695ed6cd879) (N (L 0xfffffffffff58a4ae35b0cf25b17b6) (L 0x10000000000051ec67cf3f2baa2496c))) (N (L 0xfffffffffffd84b234eb80127e0ce3) (N (L 0x100000000000130ed76f0b8568eb339) (L 0xffffffffffff6f0a7aac60961dae40)))) (N (N (L 0x10000000000004443c7bbd91ef17966) (N (L 0xffffffffffffe026404938e17ef3ff) (L 0x10000000000000eb9bfd8e98754fc92))) (N (L 0xfffffffffffff940b62408d2d2c03b) (N (L 0x1000000000000031077ee4b86cbd6d8) (L 0xfffffffffffffe9ed063b93e7be500)))))) (N (N (N (N (L 0x1000000000000009da787c74d4c08fb) (N (L 0xffffffffffffffba37fa6e18ad2656) (L 0x1000000000000001ea175d2169ef723))) (N (L 0xfffffffffffffff2aa178e750c30e5) (N (L 0x10000000000000005c254b459a87a07) (L 0xfffffffffffffffd8859beecfa4391)))) (N (N (L 0x100000000000000010c7fe4c133b144) (N (L 0xffffffffffffffff8ebf939e398465) (L 0x100000000000000002f67b23d78011e))) (N (L 0xffffffffffffffffec4e6556f8566f) (N (L 0x10000000000000000081eee63fe9e5b) (L 0xfffffffffffffffffcad0433240a3e))))) (N (N (N (L 0x100000000000000000159d28ee480ea) (N (L 0xffffffffffffffffff747795c592d0) (L 0x100000000000000000037e702b67c85))) (N (L 0xffffffffffffffffffe9c2524c0dd1) (N (L 0x100000000000000000008c9af7cb02c) (L 0xfffffffffffffffffffc8d230653e4)))) (N (N (L 0x1000000000000000000015825829965) (N (L 0xffffffffffffffffffff7abce8afb2) (L 0x1000000000000000000003343b8312f))) (N (L 0xffffffffffffffffffffec681cb906) (N (L 0x1000000000000000000000770cf5a83) (L 0xfffffffffffffffffffffd313683a5)))))))

private def cneg_lf_122 : FastDTree := dleaf cneg_bt_122 0xfffffffffff92852909495131302c8 0x100000000000422ccd32c4a0041c96d 0x1000000000000a16b26332eeafd927a 0xfffffffffffff12c0fff2c7b5872af 0x7fecf0bc889ad55f6be 0xa21966e17582ab2baa (M 0xfffffffffff9efcf9323af4d390a9c 0x10000000000028575713b4f8ca440e0 0x1000000000000873d92b44d6d358d13 0x10000000000000c320e7400a82207bc 0xfffffffffff2d2606c29915d70ed36 0x1000000000016315bade97f94661111 0x10000000000072b64881a0654e4fc15 0x1000000000036a0ce69994e25bae46b 0x87ca53e6bc7d8a7d78 (Q 0x6910b890cefa2c7d41c 0x19cf827122f66907bf16 0x3718bbc09058949e7966)) (M 0xfffffffffffb99aac0611b38d58f13 0x10000000000007dd93bea3a13b2d20e 0x100000000000056045ff2b22f944824 0x10000000000002e23b881fd7b1f67bf 0xfffffffffff32bb566eb4c5e2207ce 0x100000000000b1e436483b3d1c901dc 0xfffffffffff86b0b5b9dfab5f9a28a 0x1000000000022a321ed652173981b97 0x619c9bd965f9d32ed7 (Q 0x46d57ce63db141784ac 0x10fa025eb12c4a31e18f 0x2375144ef58d5b9827ec)) (M 0xfffffffffffd0dc1b24f2da3e55951 0xffffffffffff8ec543765784576696 0x10000000000002cf159de5790b036a1 0x10000000000003cacd74c3288921869 0xfffffffffff5bf40c8720f68af2ab9 0x10000000000047324f7abe2b13c3a58 0xfffffffffff42a00ddf93cecdb4d90 0x10000000000139efd23d2b698edf1ee 0x4b822d80cb4814b2b0 (Q 0x2fab24191d753193579 0xb2d490c704b2acc64ba 0x16ea1d967ba68aba231a)) (M 0xfffffffffffe2655e97273bac46a16 0xffffffffffff4022ac896201483575 0x10000000000000da1b6eeed774c6c2d 0x10000000000003f4fb52e632db32e9e 0xfffffffffff8b02bf4e9dc524625a1 0x1000000000000dffc2e0c6c0e4260fa 0xfffffffffff4cc7f9b24260513436a 0x1000000000009c28413c2e5abebed95 0x40c36ffe1df0d9643b (Q 0x1ff0c97e490ab8cd7eb 0x75d2ed29e180c1bc4f4 0xedb4f09c1afbad5bbcd))

private def cneg_bt_124 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff3b41fc905a40c14dd7103) (L 0x1000000005019c12607c9573ac0e250))) (N (L 0xfffffffe92cb7451f9092398f05d35) (N (L 0x10000000516e725f4c2fae4f6dab0fc) (L 0xfffffff0ea6e1771f2e8a04904ef7e)))) (N (N (L 0x1000000268c3fd964f8c5845f5551bb) (N (L 0xffffffa8e44a220fd420b9151d285c) (L 0x1000000b14185c8ffe255c460b88045))) (N (L 0xfffffeb6b68b219acadacfd4de5943) (N (L 0x1000002346f35df44a2c747e629c4b5) (L 0xfffffc7ba0db7dd6933bdc486d5eaa))))) (N (N (N (L 0x100000541ef969ad61282947fb10786) (N (L 0xfffff89793bddf94afafd42b96e4b5) (L 0x1000009e2e6014f3deef8aceb05fa20))) (N (L 0xfffff3736b2bdd7cd5ceb3e0c2d4c8) (N (L 0x100000f3493d4bb43e057fcd15b8c31) (L 0xffffee5ba76941d60caaff1a509272)))) (N (N (L 0x1000013a78d814878a3c866c391ec6e) (N (L 0xffffeaec5da674aee8a38911f2d7ef) (L 0x1000015cd8a335b28f3492f1778f3b4))) (N (L 0xffffea335b72e9cdc7b1b1a968b7d6) (N (L 0x10000151a8732dda477d06828a484dc) (L 0xffffec2ff0aa524ec8312956dd006d)))))) (N (N (N (N (L 0x1000012109da6724fc6897e3f101018) (N (L 0xffffeffb6a4da05134c52493384da5) (L 0x100000dd426b65c57c655f5ebfc8f4b))) (N (L 0xfffff45ce04e19eb3a9d43cff8cd45) (N (L 0x10000098e354b9870663d59b5fe7b40) (L 0xfffff856381b66c7e83ad2c5ae6278)))) (N (N (L 0x100000601f4df0ebd8b0234d0ecf725) (N (L 0xfffffb64688a73cddbceb539796a58) (L 0x100000375d29edb0beac7efafce100c))) (N (L 0xfffffd743844dee6f9bdbf7b2841cd) (N (L 0x1000001d63450c25eb0c0d094cefade) (L 0xfffffeb33462a32d4dfc7aac193bad))))) (N (N (N (L 0x1000000e739098da7241db445d065bd) (N (L 0xffffff6234d512e9713d4c7d7cb308) (L 0x100000069d2d80fb00115c3a505d253))) (N (L 0xffffffba3882ad64b2394c32971e08) (N (L 0x10000002d42d9cabdbe92f99f6a6452) (L 0xffffffe31bb6100e75c75594968e05)))) (N (N (L 0x10000001228511e701d4a1f0ceea303) (N (L 0xfffffff4c2b1e959ddf78f33e9670b) (L 0x100000006dae4c060ab968c04e0a42f))) (N (L 0xfffffffbe1024534866ed015fd6e1f) (N (L 0x100000002715c84c421b16e3c310f9f) (L 0xfffffffe925ebb4efcd50a79c49dc4))))))) (N (N (N (N (N (L 0x100000000d2eba1f50f675499872dd6) (N (L 0xffffffff87e9e71195d9b73b4ef4b2) (L 0x100000000437f8cdd491f49b21eb21c))) (N (L 0xffffffffda88b9e64576914bce42d6) (N (L 0x100000000148abb0e712e6895bd529d) (L 0xfffffffff4df3a99ad4cb7673e2215)))) (N (N (L 0x10000000005f526c352446fc46cb653) (N (L 0xfffffffffcd8dbb602987a69def3ee) (L 0x10000000001a65831cb9c9341753f6e))) (N (L 0xffffffffff257220e0f33a8bfc01c3) (N (L 0x100000000006fdf0542732e272b48e8) (L 0xffffffffffc75884baf163741c0d2a))))) (N (N (N (L 0x100000000001c6431b4e8cafbece3b6) (N (L 0xfffffffffff1eb04af43e6a29666d4) (L 0x1000000000006ea084af6b84cbc0dad))) (N (L 0xfffffffffffca386babcdaacebd1d5) (N (L 0x10000000000019e3c0c301265915315) (L 0xffffffffffff3a7e9bf56b8950f1da)))) (N (N (L 0x10000000000005d48974e122fab0c3d) (N (L 0xffffffffffffd45968c7081d31d0db) (L 0x1000000000000143d5c07005e45c181))) (N (L 0xfffffffffffff6b3150633c77e8170) (N (L 0x1000000000000043c69cd271b04255d) (L 0xfffffffffffffe1662b0138c6c37eb)))))) (N (N (N (N (L 0x100000000000000db2b6a34292eda90) (N (L 0xffffffffffffff9eb805627143f56c) (L 0x1000000000000002ad21ae2a5bba408))) (N (L 0xffffffffffffffed4e43d35c792381) (N (L 0x1000000000000000818733bb282e7fb) (L 0xfffffffffffffffc85abfbcfc27c00)))) (N (N (L 0x100000000000000017b7c4dc33a2519) (N (L 0xffffffffffffffff5f80ca47a3be19) (L 0x10000000000000000435c7d1676f96c))) (N (L 0xffffffffffffffffe3f0ea5cff3de1) (N (L 0x100000000000000000b99d58f978048) (L 0xfffffffffffffffffb3d21ed1c337c))))) (N (N (N (L 0x1000000000000000001f09f04a6716c) (N (L 0xffffffffffffffffff3719bc728be0) (L 0x100000000000000000050b26473ca7e))) (N (L 0xffffffffffffffffffdfcfd0d9002d) (N (L 0x10000000000000000000cc0348249fe) (L 0xfffffffffffffffffffafbbc204636)))) (N (N (L 0x100000000000000000001f5e29e9c95) (N (L 0xffffffffffffffffffff3d2add803e) (L 0x1000000000000000000004b2359d083))) (N (L 0xffffffffffffffffffffe335e59b21) (N (L 0x1000000000000000000000af5c90a62) (L 0xfffffffffffffffffffffbda9c6829)))))))

private def cneg_lf_124 : FastDTree := dleaf cneg_bt_124 0xfffffffffff926e987435fc4748dd7 0x10000000000040af9db9be9b55cec0d 0x1000000000000a24b410bad5ff29132 0xfffffffffffffb7fcc97e5b073319f 0x7f3cd1d8036a0c82b80 0xa25b7c0408f293ebf3 (M 0xfffffffffff9f2508e9af201678d37 0x1000000000002717aa0f8c3260c22d2 0x10000000000008842c537fa8dc86d89 0x100000000000015a40e624a99101bde 0xfffffffffff29c7e22b4ee3fc4ae54 0x1000000000015f46acb154f756726de 0x1000000000006a6e8309945601dbd44 0x10000000000369124c378eacc0a01d5 0x89f84028a1a0f2f6ab (Q 0x6872734ea85e09b98f5 0x19b713e8ac0664fc179a 0x36f88eea15e22b777d0f)) (M 0xfffffffffffba1105e155c54961a9d 0x10000000000007115f911abcdaa05d4 0x1000000000000577790e257382347b0 0x10000000000003629773b6039a2d3d7 0xfffffffffff31186370be79c08ba37 0x100000000000ae8be3e9ecbfe79adf7 0xfffffffffff8112268f43e1366c193 0x10000000000227b104e331da2e4bba8 0x66e143ae538e34d473 (Q 0x464a31c8401462e99c9 0x10eb20f18d3121d92bec 0x2361acfcd26f0ae70a8f)) (M 0xfffffffffffd1737b50259ff4c78b1 0xffffffffffff8804b8ed88138c179d 0x10000000000002ee84278a4010664a2 0x100000000000043aad31633336a4058 0xfffffffffff5b6efffee36fe77b33a 0x100000000000448c58aaeecf72fe6d0 0xfffffffffff3f37736209c52bff3c5 0x1000000000013702462211c31453893 0x5256439a1d00bccc5b (Q 0x2f262c9f1615db0e070 0xb245b140e17f8e96450 0x16de99f8f92a92c88640)) (M 0xfffffffffffe3021a67ed59541fd14 0xffffffffffff3df4c47701b4d1bae0 0x1000000000000101c7ac731bc412611 0x1000000000000459604dcc203858558 0xfffffffffff8b20c4e96932c0fbb37 0x1000000000000c10ca6a903ebbbb909 0xfffffffffff4afebf52520301549ad 0x10000000000099706cd23604e719cd0 0x476d8e7263853bc5c2 (Q 0x1f6d2052a88c61c5640 0x757e43de1851803ab9c 0xed4a27e74ffb29259bf))

private def cneg_bt_126 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff38e6cd0073dc5b612ae26) (L 0x10000000051ec17e225f8cd5dbf3058))) (N (L 0xfffffffe86dd76bffee0d3104a1ae6) (N (L 0x1000000054d8f1682508f9f0e2ef7b4) (L 0xfffffff0268f1607a96902233fb891)))) (N (N (L 0x100000028d33c679c0b1ceb9c602aed) (N (L 0xffffffa30c7f79030d46101daebaad) (L 0x1000000be82825e383e43732c65d6de))) (N (L 0xfffffe9ba5068453a2844bbf019c09) (N (L 0x100000266e521d330327cfb49e43a00) (L 0xfffffc24d78ae950bc836123b693e0))))) (N (N (N (L 0x1000005ccd357883c2a23ee18ccf254) (N (L 0xfffff7c74d4aa8ffe2d37994391b9e) (L 0x100000b09411c7eb0020ab8502fee56))) (N (L 0xfffff1e96a693dad92e5f6fed9df00) (N (L 0x10000112a25eb4d76d115b1029bc54c) (L 0xffffebfa348f437ea06b7951a9d690)))) (N (N (L 0x10000166c9b946cf69b2ec8560b4d21) (N (L 0xffffe7d44d18c5d48e5a5b927abbeb) (L 0x10000192126eeb16f0988676c731558))) (N (L 0xffffe6c0222dbbee64e46104e80a83) (N (L 0x10000188fd6faf2ebd2ab42c3cabc4f) (L 0xffffe8d4c2e6fcfb01c07f2a280e57)))))) (N (N (N (N (L 0x10000153933816d69a0e713d0c1c0e2) (N (L 0xffffed186642847391b4ebc9fef555) (L 0x100001064f74d0e40aa4b4a9e00e8c8))) (N (L 0xfffff22484d58007fabffcf7af1f2c) (N (L 0x100000b6d952aeb60598a2e7c8ceb9b) (L 0xfffff6cbb70dfcdcc15388394ca752)))) (N (N (L 0x10000073f08d39f617127b5496b48ed) (N (L 0xfffffa6b4a95a7d7e01fb947899c7d) (L 0x1000004354d4f8497185010384ef7df))) (N (L 0xfffffce41f6cb4e34652585a8f5464) (N (L 0x100000240737ba052babe69f4b6c053) (L 0xfffffe6666048a8b08e3421fd5f755))))) (N (N (N (L 0x10000011db1c44954bb349dda601444) (N (L 0xffffff3c48ae9287839e2329391967) (L 0x100000083c12983fce850c665ab1368))) (N (L 0xffffffa8cbcca450dc918be882f70c) (N (L 0x100000038c5ed191c0c6e3c48abe0c5) (L 0xffffffdba07716ccc1bc3161551aa8)))) (N (N (L 0x100000016f135daf2bdf459aa1a1eee) (N (L 0xfffffff1bf711d86fa74585b69b893) (L 0x100000008b9302f455d073cf2fa0df1))) (N (L 0xfffffffabcc130cf8d2e838205f6f4) (N (L 0x10000000321608973252a6610b0f70c) (L 0xfffffffe29d86c7057591ff2c06504))))))) (N (N (N (N (N (L 0x100000001102472d94d37651dfb7f0f) (N (L 0xffffffff6488b0f64b7c5d448991af) (L 0x10000000057ad4bbb843033bb8545e5))) (N (L 0xffffffffcf2c17ee6f5e493d4784a7) (N (L 0x1000000001adc00be7031ea26608b0e) (L 0xfffffffff166fc644bb9bf6107d6fc)))) (N (N (L 0x10000000007d7268a5c509869547a4f) (N (L 0xfffffffffbd65fd62e9a14a19904b5) (L 0x100000000022f5e4ea55fbb3008a657))) (N (L 0xfffffffffedda0b65f35802ef28c7b) (N (L 0x100000000009518becaf1b6d107e47b) (L 0xffffffffffb44292c0f2f13232b4ee))))) (N (N (N (L 0x10000000000261291057366e763686b) (N (L 0xffffffffffed0f055b25f7fbcf061d) (L 0x10000000000095408b386ac4ec1fc3b))) (N (L 0xfffffffffffb739bbab3f7fa36e6dd) (N (L 0x100000000000232365d26a29a1a6af9) (L 0xfffffffffffef3256a2aa673618396)))) (N (N (L 0x10000000000007f5ae63f955a5574da) (N (L 0xffffffffffffc43b6d40491891e039) (L 0x10000000000001bcb0429b07e5b6af0))) (N (L 0xfffffffffffff3312196f1fe6b1289) (N (L 0x100000000000005d9a923a995dcc575) (L 0xfffffffffffffd59e27a3641bfd873)))))) (N (N (N (N (L 0x1000000000000013067be01c507f819) (N (L 0xffffffffffffff7881ecfdb08ff1fc) (L 0x1000000000000003bce6baab53f77fe))) (N (L 0xffffffffffffffe5d16fe6ed4e5246) (N (L 0x1000000000000000b5e807e110224f3) (L 0xfffffffffffffffb1a3ab72d9c3a97)))) (N (N (L 0x1000000000000000217d8a01cfc9765) (N (L 0xffffffffffffffff1cc303fc017b38) (L 0x100000000000000005fa0ecd68dbc9a))) (N (L 0xffffffffffffffffd80f71d9ddfc32) (N (L 0x10000000000000000108e86aabe771f) (L 0xfffffffffffffffff92fdbc94ff629))))) (N (N (N (L 0x1000000000000000002c880aec53a8b) (N (L 0xfffffffffffffffffedf04cb151fb1) (L 0x10000000000000000007460c3733446))) (N (L 0xffffffffffffffffffd175b4896923) (N (L 0x1000000000000000000127bbacbc950) (L 0xfffffffffffffffffff8b59c54519a)))) (N (N (L 0x100000000000000000002db39a5ccd2) (N (L 0xfffffffffffffffffffee36bfb4bd6) (L 0x1000000000000000000006e062c8878))) (N (L 0xffffffffffffffffffffd5bd181f85) (N (L 0x1000000000000000000001020f5d473) (L 0xfffffffffffffffffffff9e2373fd7)))))))

private def cneg_lf_126 : FastDTree := dleaf cneg_bt_126 0xfffffffffff926f175c8015acd7cad 0x1000000000003f2f57cdbbb1f2a8826 0x1000000000000a4046a91cd2a7aa9c5 0x100000000000004bb816e5c898f7357 0x7e7ab8c2cea19ba4fc3 0xa41625d2796f37a7bb (M 0xfffffffffff9f621f7833dd7b8d198 0x10000000000025d48f8f4a775989315 0x10000000000008a20b90177b0d4f014 0x10000000000001e077cbc7bd521bd19 0xfffffffffff268811d1910d56bc7d9 0x1000000000015b7e24bf6b1e303193b 0x10000000000062495e153eec84337b7 0x10000000000368084de6edd0e38bed7 0x8d5b028f6ed57e277d (Q 0x67c2501c115c507adda 0x199ee75733dcff94fb4c 0x36d8dd0193b803a095d3)) (M 0xfffffffffffba991faafa646ab37bf 0x1000000000000640bd67204acb1944a 0x100000000000059c1453efa7aebc23d 0x10000000000003d30f1ea63e09afe89 0xfffffffffff2f8bc5271e0068c5fca 0x100000000000ab3cae4493ce5ca2b56 0xfffffffffff7b90c3ab22cbe9d73fc 0x100000000002252a02b374de52a8a98 0x6ca16fda008ab32077 (Q 0x45aedbbbd2e72a934cb 0x10dc4d53af60b9c2a5d5 0x234e84146547142468c9)) (M 0xfffffffffffd21a3d8772dd4025852 0xffffffffffff80ea2f5f07b3db684c 0x100000000000031b1fae19575ef0098 0x100000000000049b7af6758b9bddc86 0xfffffffffff5af9bd314c5b2472af3 0x10000000000041f02258b23855162d0 0xfffffffffff3be601c0e80e32245cc 0x10000000000134150574c2f6c4c4195 0x58e7b98d13cb967a33 (Q 0x2e946c22180af4bbb2a 0xb1b5d1085bc44a40a42 0x16d32ff70d9d6020e601)) (M 0xfffffffffffe3ac93dd668a89a0d5a 0xffffffffffff3b59c7e9277586c76c 0x100000000000013659099570bf668ca 0x10000000000004af5a30d529fd7fac5 0xfffffffffff8b49846cc2c32684f89 0x1000000000000a2b00cff424728acb3 0xfffffffffff4946f39bf5bb8f92acd 0x10000000000096bc798ecaf97b47523 0x4d6dfc14bb4749942b (Q 0x1ee0a1e5ec044639002 0x7527abf2fb8a66cc807 0xecdfa285a1500f76f3f))

private def cneg_bt_128 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff368b9d708d77f5747eb4a) (L 0x10000000053c3fbd75ce5c7f4f760cd))) (N (L 0xfffffffe7aaa63f985ceefa6efed6a) (N (L 0x10000000585fdd7676f732fbdcb7087) (L 0xffffffef5a823bd68ce9e55308722a)))) (N (N (L 0x10000002b37aa7a44649641f0a8ad4a) (N (L 0xffffff9cdcb38698e5bc086dcfa1d4) (L 0x1000000cca632339f8f07ec054f236d))) (N (L 0xfffffe7e8f50d593101a35d68dafba) (N (L 0x10000029d7d1b8fbcb86df5e95c2d9e) (L 0xfffffbc652ef1b47f135cd1376edc3))))) (N (N (N (L 0x1000006650eb0d89880d7674181f501) (N (L 0xfffff6e19ae8453057a91b30c5d1c7) (L 0x100000c4fd59f9c98780ecabdca46a6))) (N (L 0xfffff031bb312514440ecca1c45936) (N (L 0x10000135d0bbd3155ed23bb57a751e2) (L 0xffffe94a7614ff4dff2ec485f05c03)))) (N (N (L 0x10000199110cb3e5a1005091403c239) (N (L 0xffffe44cefb689d14b140234d0427b) (L 0x100001cf16da12971400529bb1b29f0))) (N (L 0xffffe2c68580a0e6405f9a2394a961) (N (L 0x100001c90e3034e60f687b9316d01bd) (L 0xffffe4ed29e1af338b8f83ebd1f4c5)))))) (N (N (N (N (L 0x1000018ea65d8b5e91cb7b5cbe74a75) (N (L 0xffffe9b481251755296d9e1c3ff34e) (L 0x10000136bda4417f11e17e63bfe3650))) (N (L 0xffffef82fa074e362a0769b7cde939) (N (L 0x100000da82fb15affcaed1c4deb2bab) (L 0xfffff4f41705a2220bc7b531552c5e)))) (N (N (L 0x1000008bbb8bf4898731611ea3ddc75) (N (L 0xfffff93eefba12151bf803af43c1ab) (L 0x10000051d1fe3c8b5b4386b23603a12))) (N (L 0xfffffc34f33869fd5d0fcb1654cfca) (N (L 0x1000002c22216d0881bd397ffb1aeec) (L 0xfffffe0846dd7da27feb84abdd0710))))) (N (N (N (L 0x100000160b59300300381e070974c61) (N (L 0xffffff0d729234a7d679128f1c6df9) (L 0x1000000a3e758fe8ddc0811e9612fb5))) (N (L 0xffffff931c6ce557d15cd5705b8665) (N (L 0x1000000472753d729a1452dca167271) (L 0xffffffd23f20790919a9300a760a0b)))) (N (N (L 0x10000001cf69cd418d6ec484c7efe5a) (N (L 0xffffffedf161934b72048d57dfb573) (L 0x10000000b176bb3b16999a9639eb282))) (N (L 0xfffffff94903004744d21a0313c246) (N (L 0x100000004020d7874cb4000346b816c) (L 0xfffffffda3f6012c28023dbd8aaaa3))))))) (N (N (N (N (N (L 0x1000000015ed4adf9436d551a95ab1c) (N (L 0xffffffff36e7cd43b01596fda1eb63) (L 0x10000000071c9f006b84a814be02f9e))) (N (L 0xffffffffc06ba3fb4901e991748749) (N (L 0x1000000002316c35fe0506d19669b92) (L 0xffffffffecde1adf7233d2cfa751de)))) (N (N (L 0x1000000000a4f253130236961800463) (N (L 0xfffffffffa825ba90f279faaf66dfa) (L 0x10000000002e4309229bff7f7039d56))) (N (L 0xfffffffffe7e8dbac3f9a892275a66) (N (L 0x10000000000c68813849c1eff7f6e89) (L 0xffffffffff9ad5dd30865cbd2b33e2))))) (N (N (N (L 0x1000000000033024c5c49fd1a0c4e3a) (N (L 0xffffffffffe68b9ee4ec6a2d65003b) (L 0x100000000000c92e6a3de26ab00e11c))) (N (L 0xfffffffffff9d9c5cfd3a3d1c0ed6b) (N (L 0x1000000000002fa5c471c7fdda88fdd) (L 0xfffffffffffe925b21e81bd0c71547)))) (N (N (L 0x1000000000000adb671e79e355ab3d8) (N (L 0xffffffffffffae3d24cc286a8259e5) (L 0x100000000000026215cb1d1327d8160))) (N (L 0xffffffffffffee60a9ffc9ad1a6a89) (N (L 0x100000000000008127cb83c2addf190) (L 0xfffffffffffffc55ad1e72b67995ec)))))) (N (N (N (N (L 0x100000000000001a6662e9054bba047) (N (L 0xffffffffffffff43762990b92b46cc) (L 0x1000000000000005373c405a683cea3))) (N (L 0xffffffffffffffdb5d932d0736cb0a) (N (L 0x1000000000000000ff3a481dc800acd) (L 0xfffffffffffffff91c11e309887a10)))) (N (N (L 0x10000000000000002f3ed3723541010) (N (L 0xfffffffffffffffebe913e8fa57555) (L 0x1000000000000000087a1815dd99a06))) (N (L 0xffffffffffffffffc733cc7cc62d7e) (N (L 0x10000000000000000179b830bbd299b) (L 0xfffffffffffffffff642907f3220b8))))) (N (N (N (L 0x1000000000000000003fd43c7dab7d5) (N (L 0xfffffffffffffffffe60b5faadaf91) (L 0x1000000000000000000a7ad677240bf))) (N (L 0xffffffffffffffffffbcc5b2b1fb88) (N (L 0x10000000000000000001ac48608a4d1) (L 0xfffffffffffffffffff56a330ada17)))) (N (N (L 0x1000000000000000000042859d37701) (N (L 0xfffffffffffffffffffe60bb7b2e5b) (L 0x100000000000000000000a0f431c448))) (N (L 0xffffffffffffffffffffc20599bcb1) (N (L 0x10000000000000000000017b652510c) (L 0xfffffffffffffffffffff6fc54e6c3)))))))

private def cneg_lf_128 : FastDTree := dleaf cneg_bt_128 0xfffffffffff9283fa6dd42d4d94ee4 0x1000000000003daa258c0ca532982e8 0x1000000000000a672d430392a82bd46 0x10000000000000ccc08373c2dd46ad9 0x7da7db8a62d955c3f38 0xa6f0d8c177618abdf3 (M 0xfffffffffff9fb1a757584882d6d6f 0x100000000000248c325d0ab9d29d851 0x10000000000008cb3a848adf3cfc840 0x10000000000002548ca5cbf8655fd10 0xfffffffffff23654968d125301986e 0x10000000000157bc0ca72148d24e60e 0x1000000000005a45d4841f4ee034dcc 0x10000000000366ef9802262bd6651f2 0x918f2391c1d1a0a86a (Q 0x6701fcf4935894c7a99 0x1986f906f40b11005401 0x36b9a14f27412de1c460)) (M 0xfffffffffffbb308975c8261983f44 0x1000000000000569dd2a105d609ce6b 0x10000000000005cbddb2689eb238cef 0x10000000000004325eaea491d84487c 0xfffffffffff2e146d167875f1e33c2 0x100000000000a7f65c88524e97e670d 0xfffffffffff762ba4bf011c6519043 0x100000000002229d825e03eb8502f3a 0x727fef0ddfb4a4296c (Q 0x4505e93040746ee068a 0x10cd87153f7d9168ff11 0x233b978eac3fd043b23e)) (M 0xfffffffffffd2ce10374162a2cdca1 0xffffffffffff79592d14feea626d0f 0x1000000000000352b1693d257fa9f44 0x10000000000004ebeaa64b75b9bee8c 0xfffffffffff5a936b9d7d0b947b8ea 0x1000000000003f5d5fad546f485790e 0xfffffffffff38aaf1d5d578c6ad4b4 0x100000000001312848f552d4bb3da09 0x5f03dd6c9c0ba9dad0 (Q 0x2df8d519cdc02a70d8d 0xb1250ea774ee7de6a35 0x16c7df422d017473facc)) (M 0xfffffffffffe4629184bfdfa54cf00 0xffffffffffff3835e1d87ae0ea623f 0x10000000000001759cc1706702898bf 0x10000000000004f596e51e36fd988d7 0xfffffffffff8b7c52e4b2da3c15c3c 0x100000000000084e0fad038174e47ba 0xfffffffffff479ff128d9b9bef4a22 0x100000000000940c7d498b7a6e8f760 0x52b70c6ef17f59a7f2 (Q 0x1e4e95c5cc625592106 0x74cf5e244fabe5480f3 0xec756c2325a7455ff53))

private def cneg_bt_130 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff34306de0a7138f87d286d) (L 0x10000000055a16d05ac9047006973bd))) (N (L 0xfffffffe6e316ab3b5393b086c939b) (N (L 0x100000005c03da469b723c81c657e05) (L 0xffffffee8603ce4605251a39048d6e)))) (N (N (L 0x10000002dbac36174db71395dc620f1) (N (L 0xffffff9650795aa243ed33b00c3054) (L 0x1000000dbb9ddd9bd0fdb5cf0f34da7))) (N (L 0xfffffe5f530f58efe35b3ea18339ae) (N (L 0x1000002d885a8785036fc877842c47e) (L 0xfffffb5f71803166ddf8e208bfd08b))))) (N (N (N (L 0x10000070bd0dca038496c5d3f1f4207) (N (L 0xfffff5e46f90d41ec189067878f680) (L 0x100000db9f13a4a52cecd6d99280736))) (N (L 0xffffee47615e5c25dac6f484008ccd) (N (L 0x1000015d45be0b16b46c407f3c32de6) (L 0xffffe642e0b2a93050d1663dd2884c)))) (N (N (L 0x100001d21257008c53ff2c02c108e34) (N (L 0xffffe04756f85961a3c261c385c972) (L 0x10000214fd6032b37e382e5527b286e))) (N (L 0xffffde32e7598ac82bf2af44198503) (N (L 0x100002132df51528a464eb5ed8dccb4) (L 0xffffe0630b1b4a4c44dd064bbdfb93)))))) (N (N (N (N (L 0x100001d3a792dac10fa3d25d4859786) (N (L 0xffffe5ba0352b3e38387356a3605e4) (L 0x1000016fd594d43ad311cc4e80841b2))) (N (L 0xffffec656399eb86f198528606de6e) (N (L 0x10000104edc431ce5ee373e99e3298f) (L 0xfffff2c0b405acf2cf637fa8026bd4)))) (N (N (L 0x100000a846c350454c01808c3abaa54) (N (L 0xfffff7d516e7a996dd6ddef2933ed2) (L 0x1000006359188094da7fd50b70aa1b8))) (N (L 0xfffffb602b7418e8ec6dc5c1dfa297) (N (L 0x1000003604af4b9c7cd1a9bba6fb84f) (L 0xfffffd950769bd5c91e9ca8bb4b535))))) (N (N (N (L 0x1000001b316bcf112132cb890f2814e) (N (L 0xfffffed3a63596a15ecd65a41e5768) (L 0x1000000cbbabf15d0dca18acaa17256))) (N (L 0xffffff78256c716c5e95b720f4cb53) (N (L 0x1000000591a3582c642819d44e7be5e) (L 0xffffffc67ed671f0eba00510983be6)))) (N (N (L 0x10000002488ae9893ae379626c76637) (N (L 0xffffffe924381cd668978cbdc526b0) (L 0x10000000e1729a0a0d4c4679db385ee))) (N (L 0xfffffff7708fec2dc6e9c113fb18fb) (N (L 0x10000000520986725b9664ad03b8b58) (L 0xfffffffcf89de5a76a9a791203301f))))))) (N (N (N (N (N (L 0x100000001c3e1bd45e33523bfddf847) (N (L 0xfffffffefc1c37b763ee7786cf7991) (L 0x100000000938c95b30fcb32059bfa7d))) (N (L 0xffffffffad48b540465a29509154fc) (N (L 0x1000000002dccc447088486f2143a9c) (L 0xffffffffe6f23b0c4bb1bdf664ff38)))) (N (N (L 0x1000000000d8b15ee55c89fca9974aa) (N (L 0xfffffffff8c37c66c084d63bcdcfe4) (L 0x10000000003d298c94141e796511720))) (N (L 0xfffffffffe00cdda69802344b26e4e) (N (L 0x10000000001081f3a06cbed16be231a) (L 0xffffffffff78ff27019879dc79b65f))))) (N (N (N (L 0x100000000004447a75224561374a692) (N (L 0xffffffffffddd2b662f2cf80fbc3d0) (L 0x1000000000010eef2ff8e408e51b6b4))) (N (L 0xfffffffffff7b19aac3c1fa21363ea) (N (L 0x100000000000408d3cab54f51a3e76c) (L 0xfffffffffffe0f2bb8b427b2dccfd4)))) (N (N (L 0x1000000000000ecbabd8677db534550) (N (L 0xffffffffffff90411747dfac035105) (L 0x10000000000003443c5b79e7e261a83))) (N (L 0xffffffffffffe7c69b8514113ce594) (N (L 0x10000000000000b20bf92725ad7b61b) (L 0xfffffffffffffaeecfb729b6bf4b15)))))) (N (N (N (N (L 0x10000000000000249974c221da6cba4) (N (L 0xfffffffffffffef9e3bcf26137322e) (L 0x1000000000000007456ed812c2d0057))) (N (L 0xffffffffffffffccc990e8543a3703) (N (L 0x100000000000000165c5575ce1794ab) (L 0xfffffffffffffff650a15028efe422)))) (N (N (L 0x100000000000000042967e504c4e7d4) (N (L 0xfffffffffffffffe39c04da41f1f9f) (L 0x10000000000000000c02fda688ab7eb))) (N (L 0xffffffffffffffffaf4de7b8b090bf) (N (L 0x1000000000000000021a116471bed1f) (L 0xfffffffffffffffff216b6367529aa))))) (N (N (N (L 0x1000000000000000005b6741e239b24) (N (L 0xfffffffffffffffffdabc200042407) (L 0x1000000000000000000f15ca33cdb27))) (N (L 0xffffffffffffffffff9efb07271da3) (N (L 0x100000000000000000026ba7e76926d) (L 0xfffffffffffffffffff0a560deac52)))) (N (N (L 0x1000000000000000000060bc565c0a9) (N (L 0xfffffffffffffffffffda299ab2a29) (L 0x100000000000000000000eb3c2eec5a))) (N (L 0xffffffffffffffffffffa5315f81ef) (N (L 0x10000000000000000000022d3f89b82) (L 0xfffffffffffffffffffff2ba2e32f8)))))))

private def cneg_lf_130 : FastDTree := dleaf cneg_bt_130 0xfffffffffff92aa6f2e2359991a317 0x1000000000003c1e88f3bcd56c62310 0x1000000000000a96fd7fd3f48d8bc55 0x100000000000013a3602cd8a50804c6 0x7cc5de7ae1ffceeebb5 0xaa927df5101987ce84 (M 0xfffffffffffa010e2ed6a04b2d3ad0 0x100000000000233d150b39cf43bdf35 0x10000000000008fd4f9e6fc17286b6d 0x10000000000002b59956927510f2126 0xfffffffffff205e4aa025e0013dea2 0x1000000000015400501cf54119143cf 0x1000000000005262eec12327fc3a757 0x10000000000365c8cf6361e7244f7c0 0x96394f14f3b00bdff1 (Q 0x66338b4100504ec17f1 0x196f45efc0fd12d3fd48 0x369ad7810d080b69ceb1)) (M 0xfffffffffffbbd4a9b5ecdd404b878 0x100000000000048b462e51d24339c81 0x10000000000006046e4b3bd62c86a1b 0x100000000000047f95eb38fadbe2992 0xfffffffffff2cb1578e345cf1e675a 0x100000000000a4b8b98924a791e442e 0xfffffffffff70e1ed74a017a443a2f 0x100000000002200be8f2d7f62f1a36c 0x78351faeacf1ef05dc (Q 0x445214e2d7027cdc201 0x10bece4dc15b09d99b2d 0x2328e598b5a2ba2379e1)) (M 0xfffffffffffd38c7701c0f8c188f97 0xffffffffffff713aa6ac438d6ce85d 0x1000000000000392d63e58d2b2fbe2a 0x100000000000052b045e1313a47f1ea 0xfffffffffff5a3b3ac2bc78b4f66e5 0x1000000000003cd3c877fbc6449548b 0xfffffffffff358586d7ce9fe39568f 0x1000000000012e3c4644426c2e4ae98 0x64887d3b9d8ba82fb7 (Q 0x2d569182929a648fd67 0xb0938f0ddec30572894 0x16bca79cb46263bc0994)) (M 0xfffffffffffe521ae4846faecb9afa 0xffffffffffff3472a19d5d88526c42 0x10000000000001bd3426e96267ecc82 0x100000000000052b18fa99c3f7dfea3 0xfffffffffff8bb88af834ae28e78e4 0x1000000000000679a5dbc88c87c6ee2 0xfffffffffff46091b628a97b2da0e6 0x10000000000091608c25def6e3c6d8c 0x5740301edb45b55186 (Q 0x1dba6cd0e2f2fbf769a 0x7475979eaadb3877232 0xec0b9004eed8bdbb176))

private def cneg_bt_132 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff31d53e50c0af299b26590) (L 0x10000000057846b6d14f84a80156921))) (N (L 0xfffffffe6171b9a3b48576e04accb5) (N (L 0x100000005fc58d820e208fd37eddcda) (L 0xffffffeda8ce8ead71e7f4c26df467)))) (N (N (L 0x1000000305dca831a7eb3312a32b606) (N (L 0xffffff8f633523eb629bfde4ce7f5c) (L 0x1000000ebcb7826d724149efcbd136a))) (N (L 0xfffffe3dcbe617de13e515965324c0) (N (L 0x10000031852828d616dae4facd2a80d) (L 0xfffffaef85c4eb1dddfd2502b79330))))) (N (N (N (L 0x1000007c261bd3a4143b041aa95d5bf) (N (L 0xfffff4cd8fcbd2461c75dfa6005a02) (L 0x100000f4b324d2c87c0a5258351a341))) (N (L 0xffffec24de668b6330c07440294421) (N (L 0x100001897f24e3419880d3ba3e21c76) (L 0xffffe2d8cf9bde23b6e0b4d3c86fec)))) (N (N (L 0x10000212a8df9c8696b9b6c7e80655f) (N (L 0xffffdbb2ac2d22d7a2a24ad03733cd) (L 0x1000026502df8dddbdd156eea79b111))) (N (L 0xffffd8eeebf913462b2caa65c2e7ab) (N (L 0x10000268e160f9c428b1ef858d5875c) (L 0xffffdb1cf3d3c3a5c5712d9010d17c)))))) (N (N (N (N (L 0x10000224330e88826c12c2b7664fd8c) (N (L 0xffffe10fad583c339a31e5a9dc0298) (L 0x100001b3171c249cb41b36880b0a2b4))) (N (L 0xffffe8b59f92ce691b2bc075fb1e96) (N (L 0x100001375755ffea50558b940137742) (L 0xfffff02037e62e4340c8a926ccc42e)))) (N (N (L 0x100000ca7e4245ccd933ec46249cdab) (N (L 0xfffff6218061d4e4e6cf973d58f6a0) (L 0x100000788907f154b6f2e7d1f096fb4))) (N (L 0xfffffa5de99e09064c5f18ab56664f) (N (L 0x1000004210798f60d09ed2cd347e97e) (L 0xfffffd0806be8d8ef75e8116c2cfdc))))) (N (N (N (L 0x100000218461f5e65abbcbffd3dafd1) (N (L 0xfffffe8c61a4a119783e57e5f23736) (L 0x1000000fd064a3c4f4a19be97508f1a))) (N (L 0xffffff56a4c2a0646c727bd1bef737) (N (L 0x10000006f7c7f4c4266c3106e44e970) (L 0xffffffb7c951468d9e12a578ae30fc)))) (N (N (L 0x10000002e0b76c8eec66e3ad64ff433) (N (L 0xffffffe31672631b14791c7a407249) (L 0x100000011e29f9f69076a927e183826))) (N (L 0xfffffff518a1d7e38369ed09409ffa) (N (L 0x1000000068dbb0c460fae7cc25df23f) (L 0xfffffffc1d84df293661383141b6fe))))))) (N (N (N (N (N (L 0x100000002458a214fbf65916af1496e) (N (L 0xfffffffeb069f24fc63e60e42cb746) (L 0x100000000bf291e2a7c2453cfcdd92f))) (N (L 0xffffffff947b299dc3ed49c1bf4c8e) (N (L 0x1000000003bba747fa6dd6a58314eaa) (L 0xffffffffdf38886b012fca6f8132e8)))) (N (N (L 0x10000000011c6c64e433fd309a2ba70) (N (L 0xfffffffff678b1315a73e5b1b453fd) (L 0x100000000050ca6f6817d13e1f6dd87))) (N (L 0xfffffffffd5aa0f5e606a0ebb0b4c6) (N (L 0x100000000015f12138c9ebb2362c1c4) (L 0xffffffffff4bffd38711e64ae201ec))))) (N (N (N (L 0x100000000005b512a66261a8657891b) (N (L 0xffffffffffd2272ba979576187f8e5) (L 0x1000000000016c8b88285d73499cc07))) (N (L 0xfffffffffff4ca56d61f495ef4861f) (N (L 0x100000000000575fd4c7ffdf57dfa10) (L 0xfffffffffffd5d8744d56f968e51f8)))) (N (N (L 0x100000000000142508d835192fed93f) (N (L 0xffffffffffff67696aee47ab25a6f1) (L 0x10000000000004792d0df30fbee7dc8))) (N (L 0xffffffffffffdebb2d6927d32ee3b8) (N (L 0x10000000000000f538c3549e557195b) (L 0xfffffffffffff90056676383500453)))))) (N (N (N (N (L 0x1000000000000032b1659cf16074d08) (N (L 0xfffffffffffffe93f1591c62f9825b) (L 0x100000000000000a209c4087eb204f9))) (N (L 0xffffffffffffffb8795a10c920b5ef) (N (L 0x1000000000000001f50cc35e379545c) (L 0xfffffffffffffff2663c8c4e6728a0)))) (N (N (L 0x10000000000000005dc31fb6d78af75) (N (L 0xfffffffffffffffd7ea6bd71d823f1) (L 0x1000000000000000110129c9271d1e4))) (N (L 0xffffffffffffffff8d7535a9ebd57a) (N (L 0x100000000000000002fdc5909bbbb25) (L 0xffffffffffffffffec264a0ee482ec))))) (N (N (N (L 0x10000000000000000082c46b5b9f044) (N (L 0xfffffffffffffffffca8c2e1cd1546) (L 0x10000000000000000015b19a2e7442d))) (N (L 0xffffffffffffffffff741e59374847) (N (L 0x100000000000000000037fb282055c3) (L 0xffffffffffffffffffe9bfee7139fe)))) (N (N (L 0x100000000000000000008c8a16e21b1) (N (L 0xfffffffffffffffffffc8e401dc500) (L 0x1000000000000000000015778c76824))) (N (L 0xffffffffffffffffffff7b148f968f) (N (L 0x100000000000000000000331b2a2e5b) (L 0xffffffffffffffffffffec79cc138b)))))))

private def cneg_lf_132 : FastDTree := dleaf cneg_bt_132 0xfffffffffff92df889a47691092e63 0x1000000000003a8b6192260cd90497b 0x1000000000000acd2d8885abffc6b6f 0x100000000000019391159ee3435517c 0x7bd6c845ee82e388009 0xaea7d698eceec55fd6 (M 0xfffffffffffa07cf93a41497e1f53b 0x10000000000021e61797f68ab730454 0x1000000000000935c20fe3df12b3ac1 0x100000000000030310ad0e536dadb02 0xfffffffffff1d71e430e92d0be790d 0x100000000001504add7a7b939dba3e1 0x1000000000004a9fc1b6c4499db7b24 0x100000000003649491a559229f157b3 0x9b0a85a6240d3e7bc5 (Q 0x6559629cf46864d9be3 0x1957cbb202aeec3106cd 0x367c7b9ef15afba73c14)) (M 0xfffffffffffbc82ca07f23fb2dadd6 0x10000000000003a3dcc5ba92031a6f3 0x10000000000006434074532308155ac 0x10000000000004ba1e1fc8b184af8d2 0xfffffffffff2b618af5c819d8510e7 0x100000000000a1839440c729d740084 0xfffffffffff6bb2cc8404c62f0f1d5 0x1000000000021d7596a3172cf32da40 0x7d8b40b915f5f2c4d1 (Q 0x439656e59f85e8b8120 0x10b023962e1fa0cd9b00 0x23166c8bc497cccf4904)) (M 0xfffffffffffd452d798ba495e340d0 0xffffffffffff687d573f2fe8fa3c71 0x10000000000003d90cad63d121e8952 0x10000000000005582a26c280c9f3095 0xfffffffffff59f061a44387fac6666 0x1000000000003a5319a7f581013bb7c 0xfffffffffff32750d90c346b77750b 0x1000000000012b512ff81abf22390d1 0x695e74be2bf6949477 (Q 0x2cb0f2c1a590f02f9f4 0xb0017d09d7b20a15434 0x16b188d5e4dd1b9e4beb)) (M 0xfffffffffffe5e76655be58d3ce239 0xffffffffffff2fff522a596ba03591 0x100000000000020aa28863ab914fa79 0x100000000000054f3d2bf61199efb62 0xfffffffffff8bfd8c9beff0e9147ec 0x10000000000004ad77eaf107cb9ed8f 0xfffffffffff4481ddd4f43255b6bef 0x1000000000008eb8b89b333749f4c87 0x5b0465f85068eb8cae (Q 0x1d27af731f46e703056 0x741a9943ad9f6fda612 0xeba218f6962591bff03))

private def cneg_sub_14 : FastDTree := (dsplit (dsplit (dsplit cneg_lf_118 cneg_lf_120) (dsplit cneg_lf_122 cneg_lf_124)) (dsplit (dsplit cneg_lf_126 cneg_lf_128) (dsplit cneg_lf_130 cneg_lf_132)))

private def cneg_bt_135 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff2f7a0ec0da4ac3ae7a2b4) (L 0x100000000596cf70d961dd273fb40f2))) (N (L 0xfffffffe546a7f7eab1964da1557f6) (N (L 0x1000000063a59ebf6cd73c81590a52b) (L 0xffffffecc29bb5ca3ff1180de659ab)))) (N (N (L 0x100000033220d9473c188d7cfa21504) (N (L 0xffffff88101aafcd77b0a9573b92fb) (L 0x1000000fce9a53a72d4c327d90f56cd))) (N (L 0xfffffe19d35e4b0d87a1fd17593b4c) (N (L 0x10000035d3ce5dfc24b8ff2317a9403) (L 0xfffffa75d588c3391623f677c09ea9))))) (N (N (N (L 0x10000088a23ae3ea6c4ba7d68e4f629) (N (L 0xfffff39a8deaaa82c055a23f84c47a) (L 0x1000011078f070ed4185ea56b348059))) (N (L 0xffffe9c424f3e253c2a325fa162f1a) (N (L 0x100001bb0847a72f65e2ebe577d71e3) (L 0xffffdf0065f94884ea797db4f9ecbd)))) (N (N (L 0x1000025bca6b737ff8160f5352fdda0) (N (L 0xffffd67bf554ea407d59a2c7fc48be) (L 0x100002c08e5bc1fc3d3beeea69d5950))) (N (L 0xffffd2e11c5bac65c38c7b2a4a4dee) (N (L 0x100002cbe55a37fcba8a1ff4bff80de) (L 0xffffd4fd9cbe9e039d50664dfe0e1a)))))) (N (N (N (N (L 0x100002822566457e2ddc671143438e7) (N (L 0xffffdb982a71039e0b61616bbb9d46) (L 0x10000202423eaa56164f18a5101a097))) (N (L 0xffffe459b9da41f7309cd92b292a01) (N (L 0x1000017335e1441c09cb89ad0a017c3) (L 0xffffecfe1f338165b0ec60b2d9c4df)))) (N (N (L 0x100000f37a94f5b309033e1b8bc0d75) (N (L 0xfffff4158d476bf11fa899b3f66db0) (L 0x100000922043d6df7d209dc4636a5ef))) (N (L 0xfffff924b4b997a25f00c4bea41384) (N (L 0x10000050bb78000816f65d23a24706d) (L 0xfffffc5ba6badf8be05351833eb443))))) (N (N (N (L 0x1000002947524127bbb38f202f68914) (N (L 0xfffffe34937b0ce25e457834de721b) (L 0x100000139fda8b0a037d8a48b2935c6))) (N (L 0xffffff2d0d5d52cf8dd06cc58b2971) (N (L 0x10000008b60e0c39d5b2322298335a9) (L 0xffffffa563db00e4cd339bda7eb77d)))) (N (N (L 0x100000039fbb8c2ffe77c13b893970b) (N (L 0xffffffdb76115bd53a045be8dabb08) (L 0x100000016aed4556cb7c599a0e209a9))) (N (L 0xfffffff21f771fe996b2a2c4ace127) (N (L 0x1000000085e9f169eef79a86c26bec9) (L 0xfffffffb0598bfecabc529a7912377))))))) (N (N (N (N (N (L 0x100000002ebc2b8765135b3596e4753) (N (L 0xfffffffe4f0a9a87f7a86b02ce7d2d) (L 0x100000000f77305aa1d9a20f6da10c0))) (N (L 0xffffffff745c8fcdcdbccb0793cdb6) (N (L 0x1000000004dd33f567baf9e699a66bc) (L 0xffffffffd5268dafdb3cdd7d3a49fa)))) (N (N (L 0x100000000174ffa082073313fce7e24) (N (L 0xfffffffff376d6b304b92cccef0467) (L 0x10000000006a9ff38831ca26d740844))) (N (L 0xfffffffffc7f397d0df2618172585c) (N (L 0x10000000001d23b0ccd63a03dfc81ef) (L 0xffffffffff10376fb3b885e83f54ec))))) (N (N (N (L 0x100000000007a04b3a0ea7868c03acb) (N (L 0xffffffffffc28d838779d2dd45f70b) (L 0x100000000001ea0fc03e1c99d27a776))) (N (L 0xfffffffffff0e2bca0c3fb65591dcf) (N (L 0x1000000000007628f3c75c65f97dad6) (L 0xfffffffffffc6d315e58d97409536c)))) (N (N (L 0x1000000000001b672348e1d37cbdffa) (N (L 0xffffffffffff2fd46fba28bc72fb0b) (L 0x100000000000061ed4e7de1d74d26b1))) (N (L 0xffffffffffffd259d7c4a91d0d87a4) (N (L 0x10000000000001516f12f395c0de336) (L 0xfffffffffffff657a17d8e034f82fe)))))) (N (N (N (N (L 0x100000000000004626401acc5e5f8ee) (N (L 0xfffffffffffffe06ce89fe9a79d9ce) (L 0x100000000000000e17af9dbd98ef973))) (N (L 0xffffffffffffff9c31fb24c6a8a317) (N (L 0x1000000000000002bd101ce4a11efff) (L 0xffffffffffffffeceb170c95fc0979)))) (N (N (L 0x100000000000000083e783b88b8e6f9) (N (L 0xfffffffffffffffc775340489f64d1) (L 0x1000000000000000180ceaa4f0e9ab0))) (N (L 0xffffffffffffffff5d90e776a61810) (N (L 0x10000000000000000440d2bcf4f9b6d) (L 0xffffffffffffffffe3b3823df29bee))))) (N (N (N (L 0x100000000000000000bae8ba9a39780) (N (L 0xfffffffffffffffffb36687d0945da) (L 0x1000000000000000001f2b1a847b764))) (N (L 0xffffffffffffffffff36827bd5bfb8) (N (L 0x100000000000000000050d7e11d4ef7) (L 0xffffffffffffffffffdfc94b38529d)))) (N (N (L 0x10000000000000000000cbfc6739262) (N (L 0xfffffffffffffffffffafcf71b6d79) (L 0x100000000000000000001f5096b0858))) (N (L 0xffffffffffffffffffff3d9f2c751e) (N (L 0x1000000000000000000004aebdbd73d) (L 0xffffffffffffffffffffe34e9a259b)))))))

private def cneg_lf_135 : FastDTree := dleaf cneg_bt_135 0xfffffffffff93204c803d4da92ceae 0x10000000000038eff0137d68eb5a79c 0x1000000000000b0722a70bcbc4c9161 0x10000000000001d8a6a1851e2b2d87d 0x7adcf46a2c5f3bfec90 0xb2e72168fea5e82008 (M 0xfffffffffffa0f3033da0a1844d0a0 0x10000000000020867af50b396e2a2e2 0x1000000000000971f862f9d697d6954 0x100000000000033cc2231f13fe4c9cc 0xfffffffffff1a9ef12bf1a87124a13 0x1000000000014c9ba642d8cdb388b47 0x10000000000042fb6ddb71f7af0bf3c 0x1000000000036353756a5eca362dec4 0x9fc1354f9b4be2dcf7 (Q 0x647631fcf822a305124 0x194088905f566b9d5fe2 0x365e89ff34c36af37d19)) (M 0xfffffffffffbd3824a9d2004c0d91f 0x10000000000002b2e5b7f33436b575e 0x1000000000000685be3e7c3b9a8a25c 0x10000000000004e1bdaa7b78c352134 0xfffffffffff2a241752f0363f7fb7f 0x1000000000009e56c0449fc710e3b60 0xfffffffffff669d7adedd50598267f 0x1000000000021adae6ef9af05742dc9 0x825a973e829bbc3988 (Q 0x42d5d3f7b5ee8296b0c 0x10a18800d5203c160590 0x23042ae6ec0483f13d11)) (M 0xfffffffffffd51e8742b124c1ef74b 0xffffffffffff5f15f70a0261791b25 0x1000000000000422c349a677b64a0b9 0x10000000000005731b58ef3f5a211a4 0xfffffffffff59b21e80ef0a5ac72a4 0x10000000000037db15b96c36bffb469 0xfffffffffff2f78dba5f30468d6afa 0x100000000001286735b96ae56a3f922 0x6d764af65e98e580ed (Q 0x2c0b5f37067ebf1bfe1 0xaf6f089754199e1605a 0x16a682c6da306c082b7c)) (M 0xfffffffffffe6b124a9cf08c510274 0xffffffffffff2ad12fdcda0e6e130a 0x100000000000025b5b996f8ed1c4a8b 0x1000000000000561bd9b43e7751a41a 0xfffffffffff8c4abcf474563a2b6f4 0x10000000000002e940854ede935c8c9 0xfffffffffff4309ab914c188037050 0x1000000000008c1513836bcd9ea8c0e 0x5e015c63f5f8147ac3 (Q 0x1c99e7f754a90dc6c6b 0x73bea6c5eb36b38e4d2 0xeb3911409819232adc5))

private def cneg_bt_137 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff2d1edf30f3e65dc1cdfd7) (L 0x1000000005b5b0fe73000dedc1afb3e))) (N (L 0xfffffffe471aeaf9c05ac6a156f437) (N (L 0x1000000067a4b7827799e85b1b54c12) (L 0xffffffebd322ef35fdce42104a8771)))) (N (N (L 0x10000003608e4d436c1f35ab38e8799) (N (L 0xffffff80522be13cc4ece9d4cce507) (L 0x10000010f23c1ba1030e328cf0261f7))) (N (L 0xfffffdf340cbb72d330903a8cb3430) (N (L 0x1000003a7a3e1dc3ff7abeb5ed37803) (L 0xfffff9f1990659a94fb1086e02543e))))) (N (N (N (L 0x10000096495740e1563d17eb5a1f836) (N (L 0xfffff248c5fe9436871758c872a5d0) (L 0x1000012f35d150e7384f3c7e2bd843c))) (N (L 0xffffe71e8b67dc799b1e64b2db13dd) (N (L 0x100001f27b7586d09cd5e9e2aa93a89) (L 0xffffdaac6d490417c1b75faf374c2b)))) (N (N (L 0x100002ae8a432286ddb71e29c8df6fe) (N (L 0xffffd08dd335c053c45c20f842a9ff) (L 0x1000032936539b4b6ea0ad756705e82))) (N (L 0xffffcbec7cc13860eadd04eeb87832) (N (L 0x1000033e36d667312dcc9c407cdc707) (L 0xffffcde35c72d9e9963d74d3c93506)))))) (N (N (N (N (L 0x100002efa5387835525d7adb3beb1b6) (N (L 0xffffd5316dba12fc4948752405cff2) (L 0x1000025f618a05cfbd73d1690a7a44a))) (N (L 0xffffdf33491a14802e17117f975f10) (N (L 0x100001ba41db8f56edc2cd91270b76b) (L 0xffffe94228cd371fe8aa0d0fb61e4a)))) (N (N (L 0x1000012488e68832c689e4224f63943) (N (L 0xfffff19fcd6dc54590e9dc12a6157a) (L 0x100000b102efd6ba25324e274ed4568))) (N (L 0xfffff7a927ef5130e3a03d42b1c90d) (N (L 0x1000006294262b2ee5facdde4a1d5cd) (L 0xfffffb89174b0bf93394228b46ceb1))))) (N (N (N (L 0x10000032cbecea5eb1611602a3f8e3e) (N (L 0xfffffdc87b9c096ffd07aa0fa4b9b4) (L 0x10000018554a2aa85a94ea1f50541eb))) (N (L 0xfffffef9760a46f926a25ef1c5e70c) (N (L 0x1000000ae1b0ffce60a745eca0a0306) (L 0xffffff8e66ab25f069a684c435b97c)))) (N (N (L 0x100000048f4ea416e04b3e4cbbc9a5a) (N (L 0xffffffd1dc88be921fcfb0ffd10150) (L 0x10000001cbe56caec7801041238f793))) (N (L 0xffffffee5a8982a2c184faea8cc0f7) (N (L 0x10000000aae05cfadf4c4fb3606fe08) (L 0xfffffff9a0442ccec42f1b75c40bd0))))))) (N (N (N (N (N (L 0x100000003c0acc46c03ce9dadc8880e) (N (L 0xfffffffdd1e481ab437928169aaf60) (L 0x1000000014009c5b2eb6a103b104211))) (N (L 0xffffffff4acd83803bdf886dba2fd3) (N (L 0x10000000065514f5cd73f0598054ef6) (L 0xffffffffc808ff387cb2269d961c68)))) (N (N (L 0x1000000001e8bb9a4a7965c39581aa8) (N (L 0xffffffffef85b232b9fc01c803e8aa) (L 0x10000000008c98bf524b8190e196b2a))) (N (L 0xfffffffffb5dcb8dca6e20495eef6b) (N (L 0x100000000026a9f256f25cea5d6976d) (L 0xfffffffffec0dc2f284a351ca6df47))))) (N (N (N (L 0x10000000000a2e5bf66904d4fad8538) (N (L 0xffffffffffadb7a4625187558ede6c) (L 0x10000000000292357791282a44272d1))) (N (L 0xffffffffffeba396b2e64cf70a9175) (N (L 0x1000000000009fa65da7ac6c5e14425) (L 0xfffffffffffb2854658b1c0aec51cf)))) (N (N (L 0x100000000000253e27b39280c749641) (N (L 0xfffffffffffee441d471dd9bdc1432) (L 0x100000000000085dcec2101f338a43e))) (N (L 0xffffffffffffc16b9d187a1a1d7bd1) (N (L 0x10000000000001cfe67dc7989a5d17d) (L 0xfffffffffffff2af66ba39b8ebb97c)))))) (N (N (N (N (L 0x1000000000000060fc30b4a82d6760a) (N (L 0xfffffffffffffd43985cf93533a983) (L 0x1000000000000013979a86b11c64dee))) (N (L 0xffffffffffffff74dd1038df2591e7) (N (L 0x1000000000000003d404e1919009ec0) (L 0xffffffffffffffe540c695db485b40)))) (N (N (L 0x1000000000000000b96449eceaca2c8) (N (L 0xfffffffffffffffb050f293a0bb9d8) (L 0x100000000000000021fc04550ee43a2))) (N (L 0xffffffffffffffff19dcf6a5d55e6e) (N (L 0x1000000000000000060ab90f7430c34) (L 0xffffffffffffffffd7b1d6deec019c))))) (N (N (N (L 0x1000000000000000010ae7d2b919b46) (N (L 0xfffffffffffffffff925505161993d) (L 0x1000000000000000002cbd3a5c6381f))) (N (L 0xfffffffffffffffffede0992f2cb74) (N (L 0x100000000000000000074a34ecf2e57) (L 0xffffffffffffffffffd167b40cdf74)))) (N (N (L 0x1000000000000000000127cc237039a) (N (L 0xfffffffffffffffffff8b6cf764e7c) (L 0x100000000000000000002da31f81aa6))) (N (L 0xfffffffffffffffffffee403b5f097) (N (L 0x1000000000000000000006dbb07bc3e) (L 0xffffffffffffffffffffd5df5ab40b)))))))

private def cneg_lf_137 : FastDTree := dleaf cneg_bt_137 0xfffffffffff9369c13d457398eb19f 0x100000000000374bd7a7572d6c56ed4 0x1000000000000b42401cb86207e0e20 0x1000000000000209a9660ac97e4c05a 0x79db03fcd27858c0b6b 0xb7118a48ae7170fdf2 (M 0xfffffffffffa17019bdf88df862b8a 0x1000000000001f1de264f8481fd77c1 0x10000000000009af57473bfa1ec8af9 0x1000000000000362db3c80b0cbc580b 0xfffffffffff17e4587d782ed6197a5 0x10000000000148f29f9557c83fda37c 0x1000000000003b751e54c2ea80817d5 0x10000000000362060aa773c62dd0601 0xa428877fa2fec500a1 (Q 0x638cdf4cef3aa4f691f 0x19297b67ad85693e6898 0x3640ff3dd9497028cd1b)) (M 0xfffffffffffbdf1f24defacef01c1a 0x10000000000001b8079238d06880132 0x10000000000006c95030ab832f9579d 0x10000000000004f6993282944db96c5 0xfffffffffff28f8160138bb00fb73e 0x1000000000009b321628b6c76d24db5 0xfffffffffff61a13aeff227662c728 0x100000000002183c30dbd5137a59b98 0x868632ed5b26cd0570 (Q 0x4213cb31ebcd0cad895 0x1092fd0ee99725d06537 0x22f21f49da5ed1f98fb9)) (M 0xfffffffffffd5ecd8b40ef94ee6763 0xffffffffffff54ff4fac1d6325c0ff 0x100000000000046d676202c7377c62b 0x100000000000057bf5ae88a62c25c67 0xfffffffffff597fb6b791f19771e55 0x100000000000356b850e106d6594d40 0xfffffffffff2c904ef1e0eda22a124 0x100000000001257e8463448c219f223 0x70c61391054be551f5 (Q 0x2b693d6b29a25268c09 0xaedc66086dcebbed0e9 0x169b955041a772a6f7e1)) (M 0xfffffffffffe77c50ea31ec7e4d697 0xffffffffffff24e37c1400ab2e51fa 0x10000000000002acd20754c5c0793d5 0x1000000000000562b2c2c00ffc67fcc 0xfffffffffff8c9f8660f6ea7f390a1 0x100000000000012cc0c42c4cb555998 0xfffffffffff419ffea063721183b02 0x1000000000008975ac2dc23016f46fc 0x6036eb914b25a85e7f (Q 0x1c1488be6798e073ec0 0x736205a360b64fee8e7 0xead082a4966cc9a2ed4))

private def cneg_bt_139 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff2ac3afa10d81f7d521cfa) (L 0x1000000005d4eb5f9e2a16fb87497fd))) (N (L 0xfffffffe39822aca1baf5de19a60b9) (N (L 0x100000006bc3833c109acf6fffea0a9) (L 0xffffffeada1a54dc70ba173985bc62)))) (N (N (L 0x10000003913b34562aac123a9fc934b) (N (L 0xffffff7824371f39dff3cca633f969) (L 0x10000012289ea4866639a4ec23cf17f))) (N (L 0xfffffdc9e930f48d08f778dc98d05e) (N (L 0x1000003f7ecae97c6c3c97d6a933e29) (L 0xfffff961fa0599999775a35f50ffd2))))) (N (N (N (L 0x100000a53544bb73acb985849b3b7d9) (N (L 0xfffff0d559831bab274bdfb9ec22ac) (L 0x10000151359f08bda6e9c1977d34fc1))) (N (L 0xffffe42cbd30b4f53712a29580cf34) (N (L 0x100002308376dc77f25836b4be42fdd) (L 0xffffd5ce305ad4483388a3a31c7431)))) (N (N (L 0x1000030c1c8c5631141916dbfb40022) (N (L 0xffffc9d037f023105f59574585ca16) (L 0x100003a0c6bae84874d8e875317db7d))) (N (L 0xffffc3f015e4bdfc5327357ea84ba2) (N (L 0x100003c21baddcabb70b8b935647a2a) (L 0xffffc5a7864c2ac21eaca2f9200edf)))))) (N (N (N (N (L 0x1000036f2e39e2198c3acc434175be2) (N (L 0xffffcdb3f706cfc9f582a2d8c785cd) (L 0x100002ccd60af42f13acaa7634524ef))) (N (L 0xffffd91eb15df4c3fcb7ab1ad7f666) (N (L 0x1000020e8159cf410830ddcc53d64ca) (L 0xffffe4cfacb91557928e13de6a24b0)))) (N (N (L 0x1000015f3493b327dfd556600e2b894) (N (L 0xffffeeab786ba00eab533fddd73c0a) (L 0x100000d6421a02f69dea665d5ebb1fb))) (N (L 0xfffff5dd917f16d3966314d6b9d940) (N (L 0x10000078467949a32247306f7317d0b) (L 0xfffffa8816fab3056783d05af5f719))))) (N (N (N (L 0x1000003e75951623f1e09342ee626fa) (N (L 0xfffffd4385426ed7a1eac14bdc8181) (L 0x1000001e25b89576bc392daafe78b2e))) (N (L 0xfffffeb984935dea229aa81f621bf2) (N (L 0x1000000d94ed73a0fba84021ff03fc3) (L 0xffffff71b241375a21225906af3bda)))) (N (N (L 0x10000005bb89844572dea81514d8b0d) (N (L 0xffffffc5c9b352eed89677fe7f7d45) (L 0x10000002464a0e3fd0f396d77d4b368))) (N (L 0xffffffe994527c8d641596297e7d15) (N (L 0x10000000d9dbb2e5886873388f73d42) (L 0xfffffff7d88180c7639b61175bb004))))))) (N (N (N (N (N (L 0x100000004d12b1e4fd2df5e861f0be0) (N (L 0xfffffffd312e2eae4ce2ac782481bc) (L 0x1000000019d9156bd276790d43718ef))) (N (L 0xffffffff1513a4c39dc6a21dc8ba18) (N (L 0x10000000083c9c57e2893384c1789e1) (L 0xffffffffb6f7e29ff4291ba9d038a5)))) (N (N (L 0x10000000027fd2bf57286763e98c1c9) (N (L 0xffffffffea5c08bae900bdc34fcf3e) (L 0x1000000000b93b1e913a2b2e60ef35c))) (N (L 0xfffffffff9e052fc168aa815566428) (N (L 0x10000000003341a96175df3dda94696) (L 0xfffffffffe579d1bfdb7d2cd1c322a))))) (N (N (N (L 0x10000000000d947cad0359936565bf8) (N (L 0xffffffffff91ea15c2573330cdc127) (L 0x1000000000037344597ffe3b3a239d6))) (N (L 0xffffffffffe4986ce3bd884f61f632) (N (L 0x100000000000d78425b4174dfc7393f) (L 0xfffffffffff9719a0002fb0cfca6e7)))) (N (N (L 0x10000000000032921d9402bfcd9f04f) (N (L 0xfffffffffffe7d988e65a8509594ac) (L 0x1000000000000b6d2631ff2ad1ad00a))) (N (L 0xffffffffffffaa49aae11de21f71d4) (N (L 0x100000000000027d306e88b91fc8a62) (L 0xffffffffffffeda8e5467dede87dd4)))))) (N (N (N (N (L 0x1000000000000085f719efca5f52fa3) (N (L 0xfffffffffffffc35d59306c48dc916) (L 0x100000000000001b369e630748130e7))) (N (L 0xffffffffffffff3e356d5e1222bc73) (N (L 0x100000000000000558b87f560090612) (L 0xffffffffffffffda8af8e6c3f48d43)))) (N (N (L 0x100000000000000104544a142c840d6) (N (L 0xfffffffffffffff8fce6fff906ed94) (L 0x10000000000000002ffa3776e97d0f2))) (N (L 0xfffffffffffffffeba3e09efa8ecb7) (N (L 0x1000000000000000089328d64dc2af5) (L 0xffffffffffffffffc6a5b063de5bf7))))) (N (N (N (L 0x1000000000000000017cc96a7f5dd8d) (N (L 0xfffffffffffffffff63223d94a6d87) (L 0x1000000000000000004028b354182ae))) (N (L 0xfffffffffffffffffe5f1b4eb6bd22) (N (L 0x1000000000000000000a81fc85aa049) (L 0xffffffffffffffffffbcaaa96903a4)))) (N (N (L 0x10000000000000000001ac87cf512c9) (N (L 0xfffffffffffffffffff56b0e0d96da) (L 0x100000000000000000004272a0e8f82))) (N (L 0xfffffffffffffffffffe617d262cd6) (N (L 0x100000000000000000000a08fb10f81) (L 0xffffffffffffffffffffc234b7c241)))))))

private def cneg_lf_139 : FastDTree := dleaf cneg_bt_139 0xfffffffffff93b8fb865ca851d1a92 0x100000000000359f1d37176f27b1c3d 0x1000000000000b7bf5d7ce8bb558ec2 0x10000000000002272916a82f1decbd4 0x78d3ccfd51456a5f7b7 0xbaf322f2f860b799a4 (M 0xfffffffffffa1f163168952e74deb5 0x1000000000001dac52ab666cdb40d73 0x10000000000009eb503c24b97e02392 0x1000000000000375e68e692cace554f 0xfffffffffff15410c9f49ab2a5b26e 0x100000000001454fc28834c2b6ad513 0x100000000000340c082fd744cfbdf29 0x10000000000360acdaf17b57ed7a94c 0xa816e5b9e2d794375e (Q 0x62a075a93ae1e0682f3 0x1912a3a4f12bc200580b 0x3623d834d50a26f60489)) (M 0xfffffffffffbead77eff87186459d1 0x10000000000000b349cd88f4f859745 0x100000000000070b6bdc096152dda39 0x10000000000004f9328e1d81527c939 0xfffffffffff27dca992d9c012de32d 0x100000000000981573ca4b95c2bcd95 0xfffffffffff5cbd57ed3a746f905b7 0x1000000000021599c7234ee86f94e06 0x89f97346deee7561f2 (Q 0x4153822443394e503e3 0x108484a3cbfd27bc96c9 0x22e048709a57820b3eed)) (M 0xfffffffffffd6bb29e550325516efb 0xffffffffffff4a3a2e015e40caad21 0x10000000000004b6737e35d10167283 0x1000000000000573340b11fdbe90006 0xfffffffffff595876d03c9e3e5ad25 0x1000000000003304362cadf4f35206b 0xfffffffffff29baccee9fb763e6bd1 0x1000000000012297462690c8875a87f 0x734813984457c2a2ef (Q 0x2acddd006fec7bc0749 0xae49cd0c2ae6c30c2b5 0x1690c0589ff5603e4870)) (M 0xfffffffffffe8465d387bcf3bfa085 0xffffffffffff1e376e926e2b780f92 0x10000000000002fc85df1694a572973 0x1000000000000552922298f4cefaea3 0xfffffffffff8cfb58a73113a327657 0xfffffffffffff77c067d3bb9a90a2c 0xfffffffffff40445783463ff1200ba 0x10000000000086da90748f37bcda26c 0x61a6bea685ea0df9e5 (Q 0x1b9aceb725f26101dc6 0x7304fc1049b0246e5a9 0xea68765d32289c0dd96))

private def cneg_bt_141 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff28688011271d91e875a1d) (L 0x1000000005f47e945adff8509081730))) (N (L 0xfffffffe2b9f6da4e47cec466a5c94) (N (L 0x100000007002af4a3c3ac40eb4ace20) (L 0xffffffe9d7366a71a979ee1964f8e1)))) (N (N (L 0x10000003c43e6eabc30d224427553b7) (N (L 0xffffff6f80d5ba8cff149ac8148c9b) (L 0x1000001372d03386609d842ef6edfcf))) (N (L 0xfffffd9d9f2298e95fb8959c8248b8) (N (L 0x10000044e8306457d2351aafa0998e4) (L 0xfffff8c612ed01e9093c8e1525d808))))) (N (N (N (L 0x100000b581e1d0f078630295f503aa8) (N (L 0xffffef3d2ab86e9296c84e9f283e65) (L 0x10000176cb3d656cb51673dd460420e))) (N (L 0xffffe0e6aad97734d8fba63ad41019) (N (L 0x10000275dd327bc93d4a82112ea9447) (L 0xffffd0555296b58f5fd9c694f4c479)))) (N (N (L 0x10000375d9feada7a05353705a99ab8) (N (L 0xffffc22815452411d0613482d9ffa4) (L 0x1000042947aaea51dc39ab0a19dacec))) (N (L 0xffffbac66f4c3f76ad9ee14ca874cd) (N (L 0x1000045a2c98424c476ecf2cf428d88) (L 0xffffbc1db32943df75a6241456bf25)))))) (N (N (N (N (L 0x100004039dd8710e7d60943acbb89d7) (N (L 0xffffc4f1fbd7591750b4181c86cc08) (L 0x1000034d651c5eb903a4d299354930c))) (N (L 0xffffd1f24864c67dc93a535efd1e1d) (N (L 0x10000272554beb9443d4c8f4c0b70c0) (L 0xffffdf84d60cf43813d45955fc2d82)))) (N (N (L 0x100001a5526d0d3e48302c266c87a8f) (N (L 0xffffeb1fce26cfbf648e764e35f4bb) (L 0x100001032452f7c557d150237d16763))) (N (L 0xfffff3b17f1560cc8f4ae5c97774d9) (N (L 0x10000092a1d01fce47feb8e4b0c148f) (L 0xfffff94ea6b8987e5abcdee506c9a3))))) (N (N (N (L 0x1000004cbd1e38b2c32fd3cfe9c10be) (N (L 0xfffffca019085d680ee7b9f1f8f278) (L 0x10000025521ceb4d7f0478dd0fc5ace))) (N (L 0xfffffe6a543a90c17e36a7b8dd47e6) (N (L 0x10000010f028a741ff634682d5ba727) (L 0xffffff4de249a6ae61a2c375695a5d)))) (N (N (L 0x100000073378a1e67b18e40243ba0b3) (N (L 0xffffffb69d90c754f31df6ef53f010) (L 0x10000002e0a4e1f207634782c8ad618))) (N (L 0xffffffe38980f98a9a417f6674db8b) (N (L 0x100000011586737069838f8981d068e) (L 0xfffffff593b05ba7730320da188dd7))))))) (N (N (N (N (N (L 0x1000000062d9eae23047b330bf9fe8e) (N (L 0xfffffffc62f91f732ae8acba3adeb8) (L 0x10000000215fa113cc335d20b964050))) (N (L 0xfffffffecfae26dc06405630e96aa7) (N (L 0x100000000ab469d5c006f3b3b197129) (L 0xffffffffa0c755925e829164718e5e)))) (N (N (L 0x100000000344e6b2862cbdc723cbe5f) (N (L 0xffffffffe39a90376b57869a9422a1) (L 0x1000000000f3d2c564395fec08e68b9))) (N (L 0xfffffffff7e9fa704868c84ea0a912) (N (L 0x100000000043e4262330ced65d98688) (L 0xfffffffffdcc27202f998f868f16df))))) (N (N (N (L 0x10000000001219093b52d38b0cb042f) (N (L 0xffffffffff6cd8b6d6741265ccba44) (L 0x100000000004a03b78bcdec1acbee23))) (N (L 0xffffffffffdb25d5f8e706db459d8c) (N (L 0x10000000000122ac7e90038c2f13c94) (L 0xfffffffffff721a009a85e23fa1c71)))) (N (N (L 0x100000000000449b6f17d8c3b0807af) (N (L 0xfffffffffffdf242ce99c499487aa1) (L 0x1000000000000f976924568ad20d53c))) (N (L 0xffffffffffff8ab5a67015019d8191) (N (L 0x100000000000036a6c12286de5933ae) (L 0xffffffffffffe6c2a80e4a5ffa1b77)))))) (N (N (N (N (L 0x10000000000000b8e0e82815613e5fe) (N (L 0xfffffffffffffac16455d5bcf3bed1) (L 0x1000000000000025c3c6bb20d3eb7a0))) (N (L 0xfffffffffffffef25480e759180d6f) (N (L 0x100000000000000775d99f2003c732f) (L 0xffffffffffffffcb978a0c5197400c)))) (N (N (L 0x10000000000000016d39187cf419e62) (N (L 0xfffffffffffffff622d859ad1011ff) (L 0x100000000000000043ab74ead31ce70))) (N (L 0xfffffffffffffffe3350ca4e1958e4) (N (L 0x10000000000000000c289263a63695c) (L 0xffffffffffffffffae76f73e6b9334))))) (N (N (N (L 0x1000000000000000021ec17b38cdf10) (N (L 0xfffffffffffffffff1fd4846516003) (L 0x1000000000000000005bec4825e5191))) (N (L 0xfffffffffffffffffda92b426b64df) (N (L 0x1000000000000000000f21ca724e572) (L 0xffffffffffffffffff9ec9e2b69a5c)))) (N (N (L 0x100000000000000000026c3ed8809c2) (N (L 0xfffffffffffffffffff0a54982fcc3) (L 0x1000000000000000000060a84b46e66))) (N (L 0xfffffffffffffffffffda389c02cca) (N (L 0x100000000000000000000eab7c648a3) (L 0xffffffffffffffffffffa5718e4b78)))))))

private def cneg_lf_141 : FastDTree := dleaf cneg_bt_141 0xfffffffffff940b2be3ad06fe5d2f2 0x10000000000033ea2479d4ce2640eb5 0x1000000000000bb1ceae38f85450d8c 0x10000000000002320f2f3e00247b53a 0x77ca4865cd7b2e11c8c 0xbe6211f41494f9e981 (M 0xfffffffffffa27420b60d6d368a6d7 0x1000000000001c322f1ccce7c25e0b1 0x1000000000000a236fbf2a40be93e67 0x1000000000000376c885541bdcb7af5 0xfffffffffff12b40b70af4ed864d92 0x10000000000141b30c6741ce42f8ac1 0x1000000000002cbf69ad4486c9743cd 0x1000000000035f4869caf2c6b458d27 0xab6c4f8bf4137d01f0 (Q 0x61b412654da62afbe23 0x18fc01394ff6c20732a6 0x360711f58e27ff4d6a84)) (M 0xfffffffffffbf681455dfa45691df7 0xfffffffffffffa511d78971eb274ff 0x1000000000000749a1f0ac0b7a7476b 0x10000000000004ea656df1bafd84a43 0xfffffffffff26d0fdd2b4cfb2d66fb 0x1000000000009500bc7e0e4b2f97679 0xfffffffffff57f1253b1d5169fc9b5 0x10000000000212f3f8703ebff53252a 0x8ca632e4b6317f29c7 (Q 0x40982fb054f7bbd94b4 0x107620f640cb4061f21e 0x22cea53014dafb71c863)) (M 0xfffffffffffd786f1916c0e2d400df 0xffffffffffff3ecd326035f2f3f73a 0x10000000000004fb7d5a2a2969760fa 0x1000000000000559ab10043a6e073fb 0xfffffffffff593bb2a29f32c0772de 0x10000000000030a4fde4142ced99a5e 0xfffffffffff26f7c22f296709e38d4 0x1000000000011fb1a2aed48acaa784b 0x74f9dc5407b82c1cf7 (Q 0x2a3c5de036a45478c57 0xadb7779a4c9311b312d 0x168603cafd903f1122a5)) (M 0xfffffffffffe90cd3a9ba25710d74b 0xffffffffffff16d4057e898a8f9c71 0x1000000000000348126f33c000105fa 0x10000000000005322ac168a9d734b32 0xfffffffffff8d5da938d5c1d36962f 0xffffffffffffdca0df3085ee29deb2 0xfffffffffff3ef63cc0ff3cd9d957f 0x1000000000008443ccd4af9cfc3df80 0x625416cf9538b73b86 (Q 0x1b2fa134fee7958b4df 0x72a7cfc0c74a3d29a3c 0xea00f51fba61321f664))

private def cneg_bt_143 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff260d508140b92bfbc9741) (L 0x1000000006146a9ca921b1ecdd578d1))) (N (L 0xfffffffe1d71e23f4229337b51a702) (N (L 0x100000007462eaf821092ec55b35aa7) (L 0xffffffe8ca2a18e8193b9b046a5627)))) (N (N (L 0x10000003f9af902f52ba7aedf375107) (N (L 0xffffff66626a4ab2184762e22340cc) (L 0x10000014d1ec07d4c06a2b81709481f))) (N (L 0xfffffd6e32a93a7a14bb614ec3bd38) (N (L 0x1000004abd98301949ab2743b4d1b3f) (L 0xfffff81cedc56fed393cfb5e9902ac))))) (N (N (N (L 0x100000c74d3d0eca712603ccd729e82) (N (L 0xffffed7cd7a83f1572325cee4ac201) (L 0x100001a051373465b69dba9bfec1261))) (N (L 0xffffdd4378badd7b6b8773e020df11) (N (L 0x100002c3597a264678a97fafd66001c) (L 0xffffca2fa33543ab2f360b3586a370)))) (N (N (L 0x100003ed43fd46ff6e9427b2e1e6d41) (N (L 0xffffb97701ac154c715fe928c96e5e) (L 0x100004c504ddfb1ca942bf48eeff667))) (N (L 0xffffb044f8ea949918f8e739b3166e) (N (L 0x10000509607774719c4ff99e6eb3f94) (L 0xffffb112f1203ab762d205c194085c)))))) (N (N (N (N (L 0x100004b041aabf9b705fb2309fccaab) (N (L 0xffffbab67075e23a870b1a8e291801) (L 0x100003e44855c5d254ac3320e6eb818))) (N (L 0xffffc97d56f746db562942f5d0a1fe) (N (L 0x100002e888e63aef3e2955d8a50db66) (L 0xffffd939bb29b6a0273767724a2461)))) (N (N (L 0x100001f90df2c8b164cde7a7783c40b) (N (L 0xffffe6df5a96bf9fc993561561e124) (L 0x100001392fdeab29bd0242e6d46e9b8))) (N (L 0xfffff111340c6f8132096cf3faa5e0) (N (L 0x100000b2a00cac7ac307afd4e2e8774) (L 0xfffff7d0ae48bd5bab4560237a25cb))))) (N (N (N (L 0x1000005e354e9cd06c30e38fa0e69ae) (N (L 0xfffffbd7653de6a5b0dc1f6a0691de) (L 0x1000002e2a0136ed0aec1cb9a0d1324))) (N (L 0xfffffe0856959c6f6d1e03b1b15488) (N (L 0x100000151b5a56a30fea8d504fd426c) (L 0xffffff213d7f1c30c3367146b94347)))) (N (N (L 0x1000000909d0979e0b52dae090053aa) (N (L 0xffffffa390840c846f8018c95ad145) (L 0x10000003a325982945ab1a61aad204c))) (N (L 0xffffffdbe57d7ad8d5e8491dcff8d9) (N (L 0x10000001613d52575d4c83a9c4d5778) (L 0xfffffff2b01e4e6c7fb5cf8e7f7ad4))))))) (N (N (N (N (N (L 0x100000007ead4480c3d8ac258200b27) (N (L 0xfffffffb5a9d49719cb9a16ba0a5cd) (L 0x100000002b0dc08f11f2d43e6759d95))) (N (L 0xfffffffe761e68a07fe6c5ffa10935) (N (L 0x100000000de67cfe18237b257638ef9) (L 0xffffffff83f401859874d7cedd5dcc)))) (N (N (L 0x100000000445be5ee743ac62cac66c5) (N (L 0xffffffffdac56597459fd1ab46d00b) (L 0x100000000140ac29cacbc655634fd17))) (N (L 0xfffffffff555075fbac25f71367c4b) (N (L 0x100000000059d8acd032807a10e9f98) (L 0xfffffffffd1383fda9c03bf0b1ead9))))) (N (N (N (L 0x10000000001818f22092f7642cbcfba) (N (L 0xffffffffff3b783d2c0278af418e6d) (L 0x100000000006325a6cd32cc7acb4cbf))) (N (L 0xffffffffffce7ca121db5b568190e0) (N (L 0x10000000000187b1e57ae489fdfa8c1) (L 0xfffffffffff40393e06e8ea94260ea)))) (N (N (L 0x1000000000005cfe631e2bb5bebde20) (N (L 0xfffffffffffd3551ccfaf0b6061182) (L 0x10000000000015417af09e0a4f92cc0))) (N (L 0xffffffffffff5fa410c9adf6d85e49) (N (L 0x10000000000004aee762fc3d95b58ed) (L 0xffffffffffffdd4bf871d4a12071f5)))))) (N (N (N (N (L 0x10000000000000fee95f7f2e50065f1) (N (L 0xfffffffffffff8bfa5bc4bf07a871a) (L 0x10000000000000345c1e02a9b3961e8))) (N (L 0xfffffffffffffe8914d7bfa7a356f5) (N (L 0x100000000000000a667f595abab3a12) (L 0xffffffffffffffb6bd79bb7f269470)))) (N (N (L 0x1000000000000001ffea109d4e21945) (N (L 0xfffffffffffffff2231f0df968e90f) (L 0x10000000000000005f5b8500964a7c3))) (N (L 0xfffffffffffffffd7519a71563a2a1) (N (L 0x10000000000000001139575882eb813) (L 0xffffffffffffffff8c314038d81365))))) (N (N (N (L 0x10000000000000000304e7f24d57afb) (N (L 0xffffffffffffffffebff20f271b791) (L 0x100000000000000000839468908ff20))) (N (L 0xfffffffffffffffffca4a0ba8a581c) (N (L 0x10000000000000000015c5633a9a5ba) (L 0xffffffffffffffffff73c8789a638c)))) (N (N (L 0x1000000000000000000380e4ed5ad40) (N (L 0xffffffffffffffffffe9bdcd3293ee) (L 0x100000000000000000008c7862126a3))) (N (L 0xfffffffffffffffffffc8f5d9baac9) (N (L 0x10000000000000000000156cd9b0c39) (L 0xffffffffffffffffffff7b6b03aac2)))))))

private def cneg_lf_143 : FastDTree := dleaf cneg_bt_143 0xfffffffffff945dab8bb03e98349b7 0x100000000000322daafe10d64c7fed1 0x1000000000000be17dc8f4631b6f457 0x100000000000022b99a51bd773db0b1 0x76c17f39faf189e7a4d 0xc13d6ff9ad0d987702 (M 0xfffffffffffa2f5bbfb3103293f91f 0x1000000000001ab034a5dea5082c279 0x1000000000000a556aa98cb5b00ecd5 0x1000000000000366ba0b0235e9a2b1d 0xfffffffffff103c5e2b78a2a624629 0x1000000000013e1c7ed38722c6ac6b3 0x100000000000258e899ee03e1e2885c 0x1000000000035dd934f0d2b4811f9cc 0xae10cd4a505af946cf (Q 0x60cad1281e36afc940b 0x18e5948c0d6d92836a05 0x35eaa9c34b6fe6dfedf5)) (M 0xfffffffffffc01f4ceb489170fa789 0xffffffffffffe8e1e171524ec37a95 0x1000000000000781ab8062856e5cba6 0x10000000000004cb61efa42105a03cc 0xfffffffffff25d447df437053c1cd2 0x10000000000091f3d91f744b68b01b9 0xfffffffffff533bfddf62e8865e48b 0x100000000002104b0f91efe6a6d8bb5 0x8e8371be6e2e75e134 (Q 0x3fe4e5ee5e0fc1519e5 0x1067d47fe2e1b312cca0 0x22bd347328f98deaa998)) (M 0xfffffffffffd84dcc0bc79b88ecff9 0xffffffffffff32c480cfdac3385813 0x100000000000053a430de8667edf0a8 0x1000000000000530839f2dd635ab9bd 0xfffffffffff5928c591b14361f8d9e 0x1000000000002e4db74f15bec562d6c 0xfffffffffff2446a1e66e6cc3ff4cc 0x1000000000011ccdbf4736dfefd7cc3 0x75dbaeaacd12f0c2a0 (Q 0x29b7967c9fcd422c2bd 0xad25a0cc03c356fcf86 0x167b5f95d934f6a78000)) (M 0xfffffffffffe9cd631326baa26a400 0xffffffffffff0ec5b598c6fc7cdbfe 0x100000000000038d3b54cb658321a79 0x10000000000005029fa12106a904321 0xfffffffffff8dc5f38b17a18704ff2 0xffffffffffffc237ea77ccad135a02 0xfffffffffff3db53a804fe5a12af85 0x10000000000081b16c856bc034102b1 0x62439d037e0d11d652 (Q 0x1ad57129862fa40cd37 0x724ac492f47d15c4046 0xe99a071e649760b47e6))

private def cneg_bt_145 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff23b220f15a54c60f1d464) (L 0x100000000634af7888ef43d06dcbcec))) (N (L 0xfffffffe0ef8b74e5c19f52bdafee3) (N (L 0x1000000078e4e77e07c40e6188d294a) (L 0xffffffe7b2a6a9e6a6733bb8a0540b)))) (N (N (L 0x1000000431a6e457f493fdd969e0629) (N (L 0xffffff5cc31f01dc9fc9d87b35964b) (L 0x10000016471add912cb417bc2eb0e8c))) (N (L 0xfffffd3b7122432ed07e9fcd0b0f08) (N (L 0x1000005106a011ce29f7db563ed9e5e) (L 0xfffff765832fc5fd5207b180c2f5d7))))) (N (N (N (L 0x100000dab7bcd91f65a0aacc89be8b4) (N (L 0xffffeb90b4cfc4f69c1c9f46a94c2e) (L 0x100001ce2a6533707ea103432e62cfc))) (N (L 0xffffd9396c3153bb11c5db1338bbc1) (N (L 0x10000319df01812de8b2bd75f6d37c6) (L 0xffffc348ec09cfc3f8b01df8c06695)))) (N (N (L 0x10000474091ef2b6228e3dbf639096a) (N (L 0xffffaf9ad33ef5cbfca9471eab1ee8) (L 0x10000576960d2e56c74773f3055a779))) (N (L 0xffffa43b621a19e6342723c3e66af6) (N (L 0x100005d3191a3caa330f92704410283) (L 0xffffa44cd6e54aa042846b8eb7514e)))))) (N (N (N (N (L 0x10000578e7eb081e34c5f015da3f8b5) (N (L 0xffffaec3ecb526b06b7f879310b2cc) (L 0x100004953fe948c4cdf4b7bd5fccf09))) (N (L 0xffffbf86f1e74a7d50c93a4ef58b81) (N (L 0x1000037463916624330d9b095358576) (L 0xffffd1bf4ebf187ce0ac4f3489654e)))) (N (N (L 0x1000025cf8df8e5aaa7753eb08cf4cf) (N (L 0xffffe1c717b28b617ab780a4b172f4) (L 0x1000017a36c78deddaee88103e5a7cb))) (N (L 0xffffede505820c05c82d577698cafd) (N (L 0x100000d96e105b2f8031b829e667ffb) (L 0xfffff5ff8e661bf88a297ad0ad28c9))))) (N (N (N (L 0x10000073904e925f1aa4307ee148aa0) (N (L 0xfffffae11a911674a7cac2c8dca0ce) (L 0x100000390eb3c7ed971f6fb41e62086))) (N (L 0xfffffd8f2d937509897095ffff4df4) (N (L 0x1000001a47c7c6830210f3944bdaaf0) (L 0xfffffee9a1da9e9663a96f084696f6)))) (N (N (L 0x1000000b55ccd5218602ef7682476e8) (N (L 0xffffff8ba9b867b21ade7b3e649b19) (L 0x10000004980a193c964e4284fca381e))) (N (L 0xffffffd23e1178b34f5b8f59951d0e) (N (L 0x10000001c13cd973316ffde885322d8) (L 0xffffffef032f39f62c997987d6984c))))))) (N (N (N (N (N (L 0x10000000a2330a2692499c335cecb87) (N (L 0xfffffffa07fd2d1dd99aa204b89af2) (L 0x10000000377eb10e6a86ab9c422fe79))) (N (L 0xfffffffe02a15a318b03406014b2b0) (N (L 0x100000001208db1a0807f1663bd2d2b) (L 0xffffffff5e8a07424923f54f9baa53)))) (N (N (L 0x100000000594305955fbbfe4f2c0775) (N (L 0xffffffffcf3b9add997f4987f3a241) (L 0x1000000001a5616bf647b1c542fd157))) (N (L 0xfffffffff1f02660cb7800cddb5f53) (N (L 0x100000000076cc7670be2cb36b2cdc3) (L 0xfffffffffc1f479a8107207964b92e))))) (N (N (N (L 0x1000000000200ee06d544af43ea913e) (N (L 0xfffffffffef9c0f844579662f131ad) (L 0x1000000000084b28946d4918750c842))) (N (L 0xffffffffffbd88d3645c3538949eb7) (N (L 0x1000000000020f5c3d3e821eb049f19) (L 0xffffffffffefd0ac4d68af8fc21c5d)))) (N (N (L 0x1000000000007defdad5567cdf99e12) (N (L 0xfffffffffffc355671cfc85c1092c6) (L 0x1000000000001cf3c281aefc3b5ec6c))) (N (L 0xffffffffffff24f3f247d411ac44cb) (N (L 0x100000000000066a537bbca5f7201fe) (L 0xffffffffffffd053d57750dfd61e2b)))))) (N (N (N (N (L 0x100000000000015f2880ccc2b6356e7) (N (L 0xfffffffffffff5fba0e53043a4c7d3) (L 0x100000000000004887b4ef7c89cb87b))) (N (L 0xfffffffffffffdf739ed66c056cac7) (N (L 0x100000000000000e7c6505daf83d58e) (L 0xffffffffffffff99af4e1a9e6849cd)))) (N (N (L 0x1000000000000002ccdf4004d93418e) (N (L 0xffffffffffffffec88e8c2e835f78f) (L 0x100000000000000086405cce7295ff9))) (N (L 0xfffffffffffffffc692f83fd1cb7c5) (N (L 0x10000000000000001860a854a88e083) (L 0xffffffffffffffff5baa3993cea704))))) (N (N (N (L 0x1000000000000000044ba369177c6d6) (N (L 0xffffffffffffffffe3777ecb97388b) (L 0x100000000000000000bc2bdb3c55520))) (N (L 0xfffffffffffffffffb2fde3f91d204) (N (L 0x1000000000000000001f4b417ad2ccb) (L 0xffffffffffffffffff35f0875d953a)))) (N (N (L 0x100000000000000000050fbbe864705) (N (L 0xffffffffffffffffffdfc338a357ce) (L 0x10000000000000000000cbf3e105513))) (N (L 0xfffffffffffffffffffafe3550a9e9) (N (L 0x100000000000000000001f43187f1f3) (L 0xffffffffffffffffffff3e12112611)))))))

private def cneg_lf_145 : FastDTree := dleaf cneg_bt_145 0xfffffffffff94ae08509d236342ba6 0x100000000000306ac14d94db3cb7d9d 0x1000000000000c08eaf301f0b1bca89 0x100000000000021553a21e60c027f05 0x75bc76e83a577547dcd 0xc36c1994457c3a80a2 (M 0xfffffffffffa373d221f7fc3cdf895 0x100000000000192772ef2577ef976b2 0x1000000000000a7f2a715092a98432e 0x1000000000000347413a1879dd2c9bb 0xfffffffffff0dd9196dc6d6f9eb44e 0x1000000000013a8c1fc26aef874310d 0x1000000000001e78b6d5c013f5de39b 0x1000000000035c5fb4a580e0043a843 0xaff31bbee400440cdf (Q 0x5fe7b780df30a66c4a3 0x18cf5e6abd9baa83f2ac 0x35ce9d0e6c1a89b91f92)) (M 0xfffffffffffc0d0d9ab84dd7fe1597 0xffffffffffffd6f7f10ff3dba7faaa 0x10000000000007b176241ba52ebd31c 0x100000000000049da544dfc82fb2a57 0xfffffffffff24e5c6567ad8e01e497 0x1000000000008eeeb7fff7b02ee2333 0xfffffffffff4e9d44025906ba71689 0x1000000000020d9f53b1f520cc329de 0x8f8c5b9e3b9a4a9369 (Q 0x3f3c7bb9daabf39ef28 0x1059a1eb35d60c10c119 0x22abf53835c087a8a4ef)) (M 0xfffffffffffd90d8722d4fa7ce130d 0xffffffffffff26315381ca575b32a5 0x1000000000000570b717c57320aec61 0x10000000000004f93377fd96e6b8680 0xfffffffffff591f12d4fcf42034206 0x1000000000002bfe43b8af4ee5ebce3 0xfffffffffff21a6e57ac757c0b2c13 0x10000000000119ebbefed2fcbcd72c3 0x75f00bcc052b86cab4 (Q 0x2941fa672544a8dd000 0xac9483aa293e5e62805 0x1670d3aa477c805653de)) (M 0xfffffffffffea85eae2028478bb9f1 0xffffffffffff061dfcf4cc4d44db80 0x10000000000003c9f86ad001e07247c 0x10000000000004c5605518215d8977e 0xfffffffffff8e33b978ef218e5c5f8 0xffffffffffffa83ee629240885a625 0xfffffffffff3c80e22c2aa93cadde6 0x1000000000007f23798ffef38778633 0x617b3c60ee390290be (Q 0x1a8e1a9c3edc89d1347 0x71ee1b9328a3e5da7f9 0xe933b40a2b58ea171bf))

private def cneg_bt_147 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff2156f16173f0602271187) (L 0x1000000006554d27fa48adfb41de37b))) (N (L 0xfffffffe00331b8759b4f303912370) (N (L 0x100000007d8958015b57f7f0468773b) (L 0xffffffe6905bc33ec1b903026d3550)))) (N (N (L 0x100000046c3d72009dd3c86debfd5b6) (N (L 0xffffff529ce3f7f9b3cb35e8d1126b) (L 0x10000017d39374a93be6baf54cf2bf0))) (N (L 0xfffffd05251f8ad0585f0748146764) (N (L 0x10000057cb60616ada36abf4adab998) (L 0xfffff69eb94bc0af2d392d3c1519c7))))) (N (N (N (L 0x100000efe449b624119532478978012) (N (L 0xffffe974c76915ce0ba04d97b82b36) (L 0x10000200c2a203cf5fbbdebecf638d7))) (N (L 0xffffd4bdd73a7c8ee74ebd21333124) (N (L 0x1000037a6c832bd64fff517e8d4b112) (L 0xffffbb8abb75c9684edc5bd79a91e3)))) (N (N (L 0x1000050c0a2ff842cf2c6908c413b5b) (N (L 0xffffa46d2f6c3af3055d2a641e006c) (L 0x10000640e8491d8b8403f53ab8d0ecc))) (N (L 0xffff9672dbbe9246dcedcb04ae8aff) (N (L 0x100006bb31a56669c83c1b0f8514d35) (L 0xffff958877389e28f811dd11ef3aa1)))))) (N (N (N (N (L 0x10000661f244783cb87182f4df8b15b) (N (L 0xffffa0d3672cc187068e5fca525268) (L 0x10000564a7cce9384bde5dd814e43b5))) (N (L 0xffffb3cca490aafe4c0964b8e5a039) (N (L 0x10000419bdc6dc69e02d60f35a3e0d8) (L 0xffffc8de232fba1d0679640d0e6ea6)))) (N (N (L 0x100002d41d663cd4fae96ee619cf965) (N (L 0xffffdbad67a74c33b03b49312124a9) (L 0x100001c8652a752927a563ad54322b4))) (N (L 0xffffea10976e44bcb14bd16e98fdc6) (N (L 0x1000010875ddeaf4e3138b173f7532c) (L 0xfffff3c99d03cc4d76c56b896b6d9a))))) (N (N (N (L 0x1000008da6337eeee5bfdc9e0dd4450) (N (L 0xfffff9b31aa3c3c7ba991884f70b04) (L 0x10000046772749e4c7df7382fbf3672))) (N (L 0xfffffcf97d3487f0449771d9fa5b87) (N (L 0x10000020b221c3f529c4800caee4277) (L 0xfffffea46c3f164378fdfd4b3eac4c)))) (N (N (L 0x1000000e344221f3dc6f93343ed7740) (N (L 0xffffff6db33edc702f907026f0d24a) (L 0x10000005cc1ffe49ff83e1d40473cc0))) (N (L 0xffffffc60dfc7982d5eeb9d17c013f) (N (L 0x100000023ada8067f27b581e887c2f0) (L 0xffffffea570d26893e36ee63064f2d))))))) (N (N (N (N (N (L 0x10000000cf82a4b11d31771efded88f) (N (L 0xfffffff85698368c47fc740a7452b6) (L 0x1000000047789f0c892865bf66de72d))) (N (L 0xfffffffd6dd59801055af7434daff3) (N (L 0x100000001760f1410298e0b994d3891) (L 0xffffffff2e04d86391e3154d33b44a)))) (N (N (L 0x10000000074750575d4803f78b2783f) (N (L 0xffffffffc02c512fe987a7f5f3eb95) (L 0x1000000002293de965ab8136ed64a2e))) (N (L 0xffffffffed7ae8b7551325b762c81a) (N (L 0x10000000009cf1f890601aa2c51c11c) (L 0xfffffffffadc7c8baeb732350ff8c5))))) (N (N (N (L 0x10000000002a9c9314b161f6032544b) (N (L 0xfffffffffea25e41548e88b95a5bf7) (L 0x10000000000b17225e365907958ce66))) (N (L 0xffffffffffa6db22e56365b6bd39bc) (N (L 0x100000000002c5642de8b477d97f79c) (L 0xffffffffffea2a22fe74723409acad)))) (N (N (L 0x100000000000aa66678e1cbe5ff8cec) (N (L 0xfffffffffffadad59449f90a39becf) (L 0x100000000000276680f70f36fcb318b))) (N (L 0xfffffffffffed50d5abdfe7aab2f4d) (N (L 0x10000000000008c7bf883b8f495b4dd) (L 0xffffffffffffbe91daf7d79fbd73a9)))))) (N (N (N (N (L 0x10000000000001e34fda2420d9bd6b6) (N (L 0xfffffffffffff22cbe5bfae9b0a8f4) (L 0x10000000000000646155f20153c74b1))) (N (L 0xfffffffffffffd2d47a9b09170ccbf) (N (L 0x1000000000000014287d1f63a8f4e86) (L 0xffffffffffffff713c29d3bddc9285)))) (N (N (L 0x1000000000000003eafb17d9ecf7808) (N (L 0xffffffffffffffe4b16f66cc4bbeeb) (L 0x1000000000000000bcd65ee6fba7b03))) (N (L 0xfffffffffffffffaf02d3c17dda824) (N (L 0x1000000000000000227882a2cc9e383) (L 0xffffffffffffffff1704137086285e))))) (N (N (N (L 0x1000000000000000061b0efb5e05930) (N (L 0xffffffffffffffffd75646b72e5262) (L 0x1000000000000000010cdaf9b054084))) (N (L 0xfffffffffffffffff91b0be876e1c3) (N (L 0x1000000000000000002cf0dd101c961) (L 0xfffffffffffffffffedd16a0c73cea)))) (N (N (L 0x100000000000000000074e33f1417b3) (N (L 0xffffffffffffffffffd15a74ee464c) (L 0x1000000000000000000127d990c6be3))) (N (L 0xfffffffffffffffffff8b80b326444) (N (L 0x100000000000000000002d92ac62f88) (L 0xfffffffffffffffffffee499e1f448)))))))

private def cneg_lf_147 : FastDTree := dleaf cneg_bt_147 0xfffffffffff94fa0f5a3316668225e 0x1000000000002ea2c25a7f1d024dd9b 0x1000000000000c263d8770fd8f3fe59 0x10000000000001f10c81937170cf2d0 0x74be1d658f9eacaa578 0xc4db9820bc064b7311 (M 0xfffffffffffa3ec3efca6e39b0103f 0x100000000000179943cbda7f9e8d703 0x1000000000000a9ed8097da5ff7f174 0x100000000000031a2856da8e0325bf8 0xfffffffffff0b895d509a573bf220a 0x1000000000013701f95c3a65c4bfc9a 0x100000000000177d479ece196281217 0x1000000000035adc5bf8f52d77ad197 0xb10794ecec194be808 (Q 0x5f0da072a310e74f591 0x18b95ff7f5ff3a04d519 0x35b2e9703fc044df9733)) (M 0xfffffffffffc17aafd5b539911a763 0xffffffffffffc4a8edc1d7090155f9 0x10000000000007d72ec10a829eb8929 0x1000000000000462f0a5e2507ad1535 0xfffffffffff2404c18b08986c87f48 0x1000000000008bf14cb650ed9f0a657 0xfffffffffff4a14607cb538ed4fe1c 0x1000000000020af1088755a4b87f1bd 0x8fbf9007a1cfba0990 (Q 0x3ea17730bb409279748 0x104b8c00cc2ff28e0161 0x229ae68ef8df2489e219)) (M 0xfffffffffffd9c42ccbda7eb97fa5f 0xffffffffffff1929727f51cb526c64 0x100000000000059d0b06ed90b7d310f 0x10000000000004b574266ecb993d43a 0xfffffffffff591e05c849e6758a00e 0x10000000000029b68a6096cdad40eb2 0xfffffffffff1f180c24797b4e29dda 0x100000000001170bc2cb94346d7784e 0x753b62bc63952faf9d (Q 0x28dd82d5865f92920d8 0xac0459f9f1107b2353e 0x16665ffb2cc821563eed)) (M 0xfffffffffffeb3485bbf69c00d753b 0xfffffffffffefcf2db2575943c03df 0x10000000000003fc805a5a482211557 0x100000000000047c1fef8bcf99249b5 0xfffffffffff8ea683a92c4b7fca34d 0xffffffffffff8eb3f5ad0fd920d721 0xfffffffffff3b58ca21c14d4c3a7c3 0x1000000000007c99fce60b0e24e6d4f 0x600201ad29c37cc40e (Q 0x1a5acbc000687c4997a 0x719211c4365fe49b40f 0xe8ce0313c6fcd4c9c84))

private def cneg_bt_149 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0xfffffffff1efbc1d18d8bfa35c4eab) (L 0x10000000067643aafd2df06d598ec77))) (N (L 0xfffffffdf1203d9f625feeadfed3e9) (N (L 0x100000008250f194a8e016be110dd12) (L 0xffffffe562f762627aa70461664f73)))) (N (N (L 0x10000004a98cff4aacb55c00342b745) (N (L 0xffffff47e96d6c978295ce78c62a7b) (L 0x10000019789b1bcae2383f88a65b2a3))) (N (L 0xfffffccb1645ae8cdc3520fc2d87cc) (N (L 0x1000005f1472c737c18e9b3598aea4c) (L 0xfffff5c7628f46e555b2abf69e0790))))) (N (N (N (L 0x10000106f87b4230b6c40b0cdc91881) (N (L 0xffffe724bf4dbb168213b7d90721cb) (L 0x100002388f8c0b847567783faa863d1))) (N (L 0xffffcfc5025a7d5a402ab158f084af) (N (L 0x100003e61b17ddfa9a2fc35c0311547) (L 0xffffb2dc29144080f64c1a629de04c)))) (N (N (L 0x100005b75fb955e06d88d9ccf9d2c20) (N (L 0xffff97c30e41b1ed34fe99a641266d) (L 0x100007274869afbaacc345e133ab044))) (N (L 0xffff86ad431e3526c7439678670914) (N (L 0x100007c60ed71e99efdf128008dbb09) (L 0xffff8479303be938ca5bed554bfc45)))))) (N (N (N (N (L 0x100007706b42fd1827a2b2421764bf1) (N (L 0xffff9092c11e7cf48c3b3977a9dcd3) (L 0x1000065790179150fbc43f2e01debdf))) (N (L 0xffffa600e5ce375bd04ff7d2dab9a2) (N (L 0x100004dd194f83838d2fa109ee2cd80) (L 0xffffbe54f8ea4759042e082def18d4)))) (N (N (L 0x100003621396926f780bb1fddd29cd7) (N (L 0xffffd460e07578582a685f94ea8d17) (L 0x100002265220c6c85d952374c4ed076))) (N (L 0xffffe571f50a9d3f4688bdfb0e9b54) (N (L 0x100001416ab096f6612e0a53ced61b2) (L 0xfffff1198770daef0cc3da452c0301))))) (N (N (N (L 0x100000ad7cdf357e361b26aacdfcec6) (N (L 0xfffff84115b1cbef4298dd9f600225) (L 0x10000056f4a6062eb5e0cb8fc22202a))) (N (L 0xfffffc40b3307d7790e44b4eb70d62) (N (L 0x10000028a51b2b94e1dd30f46d7ac7c) (L 0xfffffe4e5a9e6c270572b2f2258f14)))) (N (N (L 0x10000011c8f0be398117c3e7deeba62) (N (L 0xffffff482b5c64f70baecc9e06311a) (L 0x100000074f653cd5794f7710e8844ae))) (N (L 0xffffffb6ae34a4aaff3656e864f61f) (N (L 0x10000002d4cc0ae48bd9c132fba47c5) (L 0xffffffe467c161ea7e092747fc5d83))))))) (N (N (N (N (N (L 0x10000001094257ff1b75a4bab581144) (N (L 0xfffffff62c5e85ed7febd11ab8563b) (L 0x100000005bf8506fb695dc046e0edba))) (N (L 0xfffffffcae490e056eb982222c3551) (N (L 0x100000001e47e5eb981eb4a731572a8) (L 0xfffffffeef260959f82207364b5ae4)))) (N (N (L 0x10000000097cf29b3ae1121a28a4356) (N (L 0xffffffffac88ab7d797a8f6451fe90) (L 0x1000000002d5bf0d20b428275326e88))) (N (L 0xffffffffe7a13646182614ee06e14d) (N (L 0x1000000000cf299f9ace8da48dcd62f) (L 0xfffffffff9323c465dd75445b5cbdf))))) (N (N (N (L 0x1000000000389724475a08f57809ef3) (N (L 0xfffffffffe2e4494e771a3609a9748) (L 0x10000000000ed140e5f0c4c62456c74))) (N (L 0xffffffffff888b2e06be5c9858ef72) (N (L 0x100000000003b96bbde323037706a69) (L 0xffffffffffe2912fbd5aa6b367475f)))) (N (N (L 0x100000000000e65bcfe4d1decbcb792) (N (L 0xfffffffffff9063620ab2a0093dd71) (L 0x10000000000035926322d0478736db4))) (N (L 0xfffffffffffe685e1180bbc554c8c0) (N (L 0x1000000000000c019f51dbb8f4b8c30) (L 0xffffffffffffa646f783acef281e54)))))) (N (N (N (N (L 0x10000000000002989b6e4b714fa5b65) (N (L 0xffffffffffffecef9a92b23b23805c) (L 0x100000000000008accc4dff26d95749))) (N (L 0xfffffffffffffc15ec11c7f919660a) (N (L 0x100000000000001c06b96ba579883b0) (L 0xffffffffffffff38f919c031d97551)))) (N (N (L 0x10000000000000057a02e4707e2a9de) (N (L 0xffffffffffffffd9ba1a5585a31f75) (L 0x100000000000000109608a7a66336ae))) (N (L 0xfffffffffffffff8de21beac04a2dc) (N (L 0x100000000000000030b2d2a47e869c6) (L 0xfffffffffffffffeb5fd90cbae2b55))))) (N (N (N (L 0x100000000000000008abc00b5438060) (N (L 0xffffffffffffffffc61a8f18323a25) (L 0x1000000000000000017fc889c311925))) (N (L 0xfffffffffffffffff62221974c68ac) (N (L 0x100000000000000000407acf14039bb) (L 0xfffffffffffffffffe5d8d724bfd8e)))) (N (N (L 0x1000000000000000000a88e06b2b484) (N (L 0xffffffffffffffffffbc90de75e836) (L 0x10000000000000000001acc1e52e189))) (N (L 0xfffffffffffffffffff56bfb515376) (N (L 0x10000000000000000000425f8dc40a1) (L 0xfffffffffffffffffffe623d4fe2ff)))))))

private def cneg_lf_149 : FastDTree := dleaf cneg_bt_149 0xfffffffffff953fd66ed059efa5f15 0x1000000000002cd7496de7a9c29e3f5 0x1000000000000c37e5c408af31f2a1c 0x10000000000001c0cd4f3039de4ca0b 0x73c935823c3ec752219 0xc57f2f404085313d97 (M 0xfffffffffffa45d263b949c769cbb8 0x1000000000001607412c534bcfa6853 0x1000000000000ab2e527a5989509217 0x10000000000002e1734d09ff23a800f 0xfffffffffff094c5583ad472664b6b 0x100000000001337e19bb1c547b4f7fc 0x100000000000109b994c5e00f6719e3 0x100000000003594f990d6c1be103de8 0xb1474fda8a833e6003 (Q 0x5e3f289116aa55d4e6e 0x18a39a98d7cc487883d1 0x35978ca75dd74c1da2c0)) (M 0xfffffffffffc21b0b2f5b05bcf1a5a 0xffffffffffffb20e71ccd1653021c1 0x10000000000007f14ab478074865655 0x100000000000041d3ecf14e9c4eed3f 0xfffffffffff23308bbbd269a170506 0x10000000000088fb8fcedb570b1dda2 0xfffffffffff45a0c270ca6b597a69a 0x10000000000208406e8718298180f0d 0x8f1e9851e7641eb3ba (Q 0x3e15f97a17ffb55da7c 0x103d9593ff6e53f2ea22 0x228a0796ab15fd9d1988)) (M 0xfffffffffffda700c5d0d93fe47d6a 0xffffffffffff0bc6940bd44b1a270d 0x10000000000005bdb88e1e18e1593e7 0x100000000000046738829eb87124b54 0xfffffffffff5925123ae80517f33c0 0x1000000000002776782189db0fe0ef7 0xfffffffffff1c999a960920adb7d7a 0x100000000001142de9ab0a155d3fa53 0x73c3d0c24f38596d74 (Q 0x288b9ae2e9a627b5fa4 0xab755b110da5ea950bf 0x165c047c844b728f6f11)) (M 0xfffffffffffebd792adfa535bebd67 0xfffffffffffef35e3259a245262609 0x10000000000004235194c67850af68b 0x1000000000000428ca85271fa89954d 0xfffffffffff8f1de1f1e1b3cd4638d 0xffffffffffff75959bf9309d0552a3 0xfffffffffff3a3c8d67028476314b7 0x1000000000007a14fe7671e253ff792 0x5ddffdf86786913daf (Q 0x1a3bf4f019e8c0e02cc 0x7136df132339d020e44 0xe868faeb7c10df32023))

private def cneg_sub_15 : FastDTree := (dsplit (dsplit (dsplit cneg_lf_135 cneg_lf_137) (dsplit cneg_lf_139 cneg_lf_141)) (dsplit (dsplit cneg_lf_143 cneg_lf_145) (dsplit cneg_lf_147 cneg_lf_149)))

private def cneg_node_16 : FastDTree := dsplit cneg_sub_14 cneg_sub_15

private def cneg_node_17 : FastDTree := dsplit cneg_node_13 cneg_node_16

private theorem cneg_ok_11 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f true cneg_sub_11 8 4 = true := by
  decide

private theorem cneg_ok_12 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f true cneg_sub_12 9 4 = true := by
  decide

private theorem cneg_nok_13 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f true cneg_node_13 4 3 = true := by
  rw [show cneg_node_13 = dsplit cneg_sub_11 cneg_sub_12 from rfl]
  exact checkFastDTree_dsplit _ _ _ _ _ _ _ _ _ _ cneg_sub_11 cneg_sub_12 4 3 8 9 4 rfl rfl rfl cneg_ok_11 cneg_ok_12

private theorem cneg_ok_14 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f true cneg_sub_14 10 4 = true := by
  decide

private theorem cneg_ok_15 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f true cneg_sub_15 11 4 = true := by
  decide

private theorem cneg_nok_16 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f true cneg_node_16 5 3 = true := by
  rw [show cneg_node_16 = dsplit cneg_sub_14 cneg_sub_15 from rfl]
  exact checkFastDTree_dsplit _ _ _ _ _ _ _ _ _ _ cneg_sub_14 cneg_sub_15 5 3 10 11 4 rfl rfl rfl cneg_ok_14 cneg_ok_15

private theorem cneg_nok_17 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f true cneg_node_17 2 2 = true := by
  rw [show cneg_node_17 = dsplit cneg_node_13 cneg_node_16 from rfl]
  exact checkFastDTree_dsplit _ _ _ _ _ _ _ _ _ _ cneg_node_13 cneg_node_16 2 2 4 5 3 rfl rfl rfl cneg_nok_13 cneg_nok_16

end GaussSmallBridge

theorem solution (δ : ℝ) (hd_lo : -(3 / 4) ≤ δ) (hd_hi : δ ≤ -(1 / 2)) {t : ℝ}
    (hlo : -(23 / 16) ≤ t) (hhi : t ≤ -1) :
    ‖mellin (fun u : ℝ => (Real.exp (-u ^ 2 / 2) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ)))
      ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖mellin (fun u : ℝ => (Real.exp (-u ^ 2 / 2) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ)))
        ((1 / 2 : ℂ) - Complex.I)‖ := by
  apply GaussSmallBridge.sound_subtree_lit true GaussSmallBridge.cneg_node_17
    2 2 (by norm_num) GaussSmallBridge.cneg_nok_17 δ _ hlo hhi
  rw [abs_le]; norm_num [GaussSmallBridge.signB]; constructor <;> linarith

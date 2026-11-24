-- Prove2me | solution 1 for GaussianMellinBound.small_delta_p4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T03:33:07.778689+00:00
-- url     : https://prove2.me/submissions/fd7ec577-d7d6-49a1-a4db-b3a6f0cfe7f6

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

private def cpos_bt_227 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0x100000000004b65f1fccc8cbd9585b9) (L 0x100000000048b1a72317b08e873c4e7))) (N (L 0x100000000015461cf67bb771b12859b) (N (L 0x1000000000a520b8df5efeabadb3310) (L 0x100000000030051290b81ea45ccd06e)))) (N (N (L 0x1000000000fa0c849d35a36f60c8268) (N (L 0x10000000004842b308cb40f8e72dc29) (L 0x10000000011bf71f5327d67113b2587))) (N (L 0x1000000000518da4446f99d3f532a84) (N (L 0x100000000101f881e6e9d8ca5dcc21e) (L 0x100000000049a1eff10c0164d998f5c))))) (N (N (N (L 0x1000000000c34907134e326885b9c8c) (N (L 0x10000000003766959ca6a0ae75a66b6) (L 0x10000000007eb4bd866cd2080b6b3a4))) (N (L 0x100000000023ba71ceaf8af5b8d4096) (N (L 0x100000000047ee0836614931209f051) (L 0x1000000000142941f99d7de16772f8d)))) (N (N (L 0x1000000000244b77882f55b3b75db98) (N (L 0x10000000000a1cd5fe574eaab0c6b4d) (L 0x1000000000107b48abbca4926444375))) (N (L 0x10000000000490ad2a10f07bc59e3c9) (N (L 0x100000000006cdb75effcac77a5033c) (L 0x100000000001df9c8e65e37d9ffbd08)))))) (N (N (N (N (L 0x1000000000029307821e41ad440a7ca) (N (L 0x100000000000b46c95fc1f4849581c0) (L 0x100000000000e62b5af02ea723ac8e4))) (N (L 0x1000000000003ea6f30b33ac3f33de5) (N (L 0x1000000000004aa45bf475738c97a31) (L 0x1000000000001433ab706b45d486973)))) (N (N (L 0x100000000000169747cf605feb7cd22) (N (L 0x100000000000061465efba7c7fd7a81) (L 0x1000000000000668df5f985be79b215))) (N (L 0x10000000000001b71df2d740ec9db05) (N (L 0x10000000000001b627078a86f1466f8) (L 0x10000000000000749a53c801e39bb15))))) (N (N (N (L 0x100000000000006e7df843b7a2daa72) (N (L 0x100000000000001d3e0cceef1174e8a) (L 0x100000000000001a65548f32062217f))) (N (L 0x1000000000000006f294aa8470f2832) (N (L 0x1000000000000005fd7ec583d0903b3) (L 0x1000000000000001916fa1260d99fe7)))) (N (N (L 0x10000000000000014b6bd257773f7de) (N (L 0x1000000000000000564aa2226a642a5) (L 0x1000000000000000445e4971f885fdf))) (N (L 0x100000000000000011b4adca40c0bc4) (N (L 0x10000000000000000d7d61c2759c4e9) (L 0x1000000000000000037999ae219ef77))))))) (N (N (N (N (N (L 0x1000000000000000028cf7b5f9010de) (N (L 0x100000000000000000a7521de301bcb) (L 0x10000000000000000076850fcd2848c))) (N (L 0x1000000000000000001e362e56088c3) (N (L 0x10000000000000000014af24b9b4e2f) (L 0x100000000000000000053ec6e51f68c)))) (N (N (L 0x1000000000000000000379d8fdbebca) (N (L 0x10000000000000000000e07e0495d93) (L 0x1000000000000000000090312116b9d))) (N (L 0x100000000000000000002430f26a314) (N (L 0x10000000000000000000168ef2629ae) (L 0x1000000000000000000005a2200ab24))))) (N (N (N (L 0x100000000000000000000369522f8a4) (N (L 0x1000000000000000000000d8fd3bb93) (L 0x10000000000000000000007fcd9e05a))) (N (L 0x10000000000000000000001f988f2ba) (N (L 0x1000000000000000000000121e2354c) (L 0x10000000000000000000000474f86dd)))) (N (N (L 0x1000000000000000000000027d909f7) (N (L 0x1000000000000000000000009c113d9) (L 0x100000000000000000000000550f3f3))) (N (L 0x10000000000000000000000014b83d3) (N (L 0x1000000000000000000000000b05fdf) (L 0x10000000000000000000000002ac130)))))) (N (N (N (N (L 0x10000000000000000000000001638c0) (N (L 0x1000000000000000000000000055c5b) (L 0x100000000000000000000000002b956))) (N (L 0x100000000000000000000000000a76b) (N (L 0x100000000000000000000000000533a) (L 0x10000000000000000000000000013e2)))) (N (N (L 0x10000000000000000000000000009ad) (N (L 0x100000000000000000000000000024c) (L 0x1000000000000000000000000000118))) (N (L 0x1000000000000000000000000000042) (N (L 0x100000000000000000000000000001e) (L 0x1000000000000000000000000000007))))) (N (N (N (L 0x1000000000000000000000000000003) (N (zL) (zL))) (N (zL) (N (zL) (zL)))) (N (N (zL) (N (zL) (zL))) (N (zL) (N (zL) (zL)))))))

private def cpos_lf_227 : FastDTree := dleaf cpos_bt_227 0xffffffffffc753dbe8817a3bb3f78e 0x1000000000076525149251c306d86b6 0x1000000000009d6b2cb9c9181618e6f 0x1000000000026a903df62ef8d596685 0x83318db1342dfc797d54 0x27e47b36d0ac7b3263ed (M 0xffffffffffc2a5c446bb7a9f5740b7 0x100000000006ab788b9a153557c8871 0x10000000000070a2fc06ac088dc7692 0x100000000002620cb696bf5480715a2 0x100000000003facd0df1e0966f52425 0x10000000000b460b68d685373c1482d 0x10000000000a92fbe6b28607beef3bd 0x10000000000569f37bf33c9079d315f 0x26c5c66766629d42c6c5 (Q 0x7b1894db2bd031805c68 0xbf496f54f52de8fd18cb 0xbe127a95a8bd578ef567)) (M 0xffffffffffbd0ce1cf49dd09020469 0x10000000000558e33bdaeec39608bbd 0x1000000000001f235af742a50dac932 0x10000000000247686f12222998553fe 0x100000000001bf68e2c92e82eca4f18 0x100000000009e0f9a414a7175a1fe5e 0x10000000000771e29372839f76c1791 0x100000000005a36cf70a7c1d19115f9 0x2483d06970b271e24738 (Q 0x6ca313386fd146d16318 0xa083f287e84146bb6407 0x956ca3060f8a619307b4)) (M 0xffffffffffbb35e01be94fcf97ed1f 0x100000000004331de56918caefb598a 0xfffffffffffd9446af9b59f1f902ea 0x10000000000222e87f25bcac859abc2 0x1000000000002ff6610cd0c2e94183d 0x1000000000087dd77c0386b28c01204 0x1000000000052822c7284f6ba16df3e 0x10000000000568d2b10cdd680bcf430 0x2244730fbaec0bebcfb2 (Q 0x60297d8da49bea89e717 0x87e5eef7ef76f1685402 0x7793ddf9b45e7a8f9ae4)) (M 0xffffffffffbbf96c887183fb3df5f5 0x100000000003387cabf262d7bf53707 0xfffffffffff9f4b1bda3628d03c387 0x100000000001f7cc427314b66358be3 0xfffffffffff1e5816943ff65a563e3 0x10000000000730e99d817e1c8e4652e 0x1000000000037aea2739961eca29e30 0x100000000004f91110f1887c691658d 0x200fee400be2bfafddde (Q 0x5556fcfbcc40be102731 0x73eb0fa56e67d7ccf6a1 0x611d7cbee9febe4a12a4))

private def cpos_bt_229 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0x10000000000e231d5f665a638c0912c) (L 0x10000000004e3ee03bd53502c11ec25))) (N (L 0x10000000004174ec94a7a2fdfdfad5b) (N (L 0x1000000000be82f643131feecd5f3bd) (L 0x1000000000977d00fc1d5e51e860499)))) (N (N (L 0x100000000134136acb5fbb9ce2b637f) (N (L 0x1000000000e9a84e9ef4a831cfdffda) (L 0x100000000174645a61f57dd80cd8a30))) (N (L 0x10000000010e3789fb24fcbb3347361) (N (L 0x1000000001670747f91ac2f8748cf44) (L 0x1000000000f9ececb653f762b5c5c86))))) (N (N (N (L 0x10000000011fac71ff3da517ec81f31) (N (L 0x1000000000c093e3a730850ec9aa863) (L 0x1000000000c5164a2868f9466065983))) (N (L 0x10000000007f27efc1744c27a24448e) (N (L 0x100000000075e229dfffacfa24ab3ad) (L 0x10000000004971e272348b338677852)))) (N (N (L 0x10000000003e8c046316bdaa688d92f) (N (L 0x100000000025b2c6aead506d5e48b44) (L 0x10000000001dcfc4149a7578c470e98))) (N (L 0x1000000000116927177e7700114e173) (N (L 0x10000000000ce5189644abb351919a9) (L 0x1000000000074eeb396d7db3a0905b4)))))) (N (N (N (N (L 0x1000000000051aca36fe36d499754b7) (N (L 0x100000000002cfb76feea7d037fc986) (L 0x100000000001dccf1383e63fd03b4fd))) (N (L 0x100000000000ff825136ad7569d95ad) (N (L 0x100000000000a152a8e302656df75dc) (L 0x10000000000054360ae29dd1372e79f)))) (N (N (L 0x10000000000032e088e0932806af3dc) (N (L 0x10000000000019e604340ecf4e029a9) (L 0x1000000000000f06375239f20ffcd95))) (N (L 0x10000000000007772b2240a411f01d4) (N (L 0x100000000000042bc84b6ff4b19c683) (L 0x100000000000020666410c11b907b41))))) (N (N (N (L 0x1000000000000117ab45fa5a9853645) (N (L 0x1000000000000084c697bfdb707b20a) (L 0x1000000000000045531f2d7d8ae6bb2))) (N (L 0x1000000000000020360e8411e4a8079) (N (L 0x10000000000000104f40912b4b563c2) (L 0x10000000000000076c16ca947f6017c)))) (N (N (L 0x1000000000000003a6ab80b5a6606f6) (N (L 0x1000000000000001a0e61aabd5063c9) (L 0x1000000000000000c78de7b0f67b418))) (N (L 0x1000000000000000574c4a4cf5c1c49) (N (L 0x100000000000000028b8563433e8b57) (L 0x1000000000000000117b6e6d9cd2918))))))) (N (N (N (N (N (L 0x100000000000000007f4f222fc0588c) (N (L 0x1000000000000000035abf984a3752b) (L 0x1000000000000000017dd359d58e649))) (N (L 0x1000000000000000009e28b10782a04) (N (L 0x10000000000000000044c5c93502f88) (L 0x1000000000000000001c00f29203312)))) (N (N (L 0x1000000000000000000beb996b1d48c) (N (L 0x10000000000000000004c61fd464408) (L 0x10000000000000000001fdb7e8204b4))) (N (L 0x10000000000000000000c8de4814f62) (N (L 0x1000000000000000000052277dc780f) (L 0x100000000000000000001fdf0a5f742))))) (N (N (N (L 0x100000000000000000000ccae020002) (N (L 0x1000000000000000000004e33a91cad) (L 0x1000000000000000000001ed37754d2))) (N (L 0x1000000000000000000000b9aa10a8b) (N (L 0x100000000000000000000047ebfd9c8) (L 0x10000000000000000000001aaf5e378)))) (N (N (L 0x10000000000000000000000a2a2e440) (N (L 0x100000000000000000000003b7f68eb) (L 0x10000000000000000000000164c69bb))) (N (L 0x10000000000000000000000080bcddd) (N (L 0x1000000000000000000000002f7f04a) (L 0x10000000000000000000000010e8f23)))))) (N (N (N (N (L 0x1000000000000000000000000625005) (N (L 0x1000000000000000000000000228bea) (L 0x10000000000000000000000000c5e92))) (N (L 0x1000000000000000000000000044a93) (N (L 0x10000000000000000000000000183c2) (L 0x10000000000000000000000000084da)))) (N (N (L 0x1000000000000000000000000002e3e) (N (L 0x1000000000000000000000000000fa6) (L 0x100000000000000000000000000055f))) (N (L 0x10000000000000000000000000001cb) (N (L 0x100000000000000000000000000009a) (L 0x1000000000000000000000000000032))))) (N (N (N (L 0x1000000000000000000000000000010) (N (L 0x1000000000000000000000000000005) (L 0x1000000000000000000000000000001))) (N (zL) (N (zL) (zL)))) (N (N (zL) (N (zL) (zL))) (N (zL) (N (zL) (zL)))))))

private def cpos_lf_229 : FastDTree := dleaf cpos_bt_229 0xffffffffffaf4bd9988e76a43e7e7a 0x1000000000079ae9fd3ab8f657f390d 0x100000000000153007a3fae972a3835 0x100000000002a8fee936c8bdb8fe36b 0x92032e10c439feab5b1c 0x2a95348e83acad11429f (M 0xffffffffffab1243b7d4642b96c499 0x100000000006c66e605547ccb109e97 0xfffffffffffe7369723f4290752fcd 0x10000000000298ae6c32c25493288e6 0x10000000000375dea9a77126afccb5f 0x10000000000ce59f4939639ef8945ac 0x10000000000b8d94004cbff37c05a20 0x1000000000064565245073c9e852222 0x29924b6300e1414fff88 (Q 0x89b596bedb30f43977ad 0xd5a6703f4060f6dc0f97 0xd2532de6271dc06a0a2c)) (M 0xffffffffffa6bbe1679af5441a4d77 0x10000000000543761dc41e009dc9719 0xfffffffffff94f78b3e1d6f68d549e 0x1000000000026eb980df9420334e8ec 0x10000000000104cc84d62d5ba588b96 0x10000000000b46be3591cf27afbdc46 0x100000000008258e0e731e79d37e604 0x1000000000069315a068dd37599a13f 0x277db28841c62d16d290 (Q 0x7ab8fa0065f7cf962ff3 0xb527ff8f768ba42d91fe 0xa77fbd97346e93c1f5f2)) (M 0xffffffffffa68180e7cfd1e459393e 0x100000000003f4bf4c46f73c8bfefaf 0xfffffffffff505dad43efb30ce8881 0x1000000000023b8ff9889e30bee373e 0xfffffffffff509c7dca533e592953a 0x100000000009a710b84763522069d0f 0x1000000000059bd212e9f3fbe187fc3 0x1000000000065afe21cf9c309504b44 0x255f05f95b8f5ea3cccd (Q 0x6d9db3b5a082f2f8e919 0x9ad48266d1683ad3e478 0x879f366f2e8e2196f853)) (M 0xffffffffffa91bec4047b512be196d 0x100000000002d8b57bceea9a0d82cde 0xfffffffffff19717d3b9e583422e88 0x10000000000202b629d2f824ebdf10d 0xffffffffffe29188c31448a63f0cab 0x1000000000081ea79f1deab5f58fe10 0x100000000003b818b777e32e54a183c 0x100000000005e1041547d1f940d5455 0x233fd62c16757510122a (Q 0x621a86197dc0099845e6 0x85353d30c7cdc7ce6fc6 0x6f4e34309ae9decd76e4))

private def cpos_bt_231 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0x1000000000178fdb9effebfb3eb9c9f) (L 0x10000000005959526d503deb34e3aa2))) (N (L 0x1000000000728b7d467104850a52aa7) (N (L 0x1000000000f334933911a1e8c26f57b) (L 0x100000000115cf88a9a830937f689f7)))) (N (N (L 0x1000000001b0fe38ef61647b2ed6ae8) (N (L 0x1000000001c0469ec2a13dce4b00316) (L 0x100000000239a2809f4f0e62a6c9536))) (N (L 0x10000000021d7b6d0294950ea56635e) (N (L 0x100000000250693f65d0034820a58a6) (L 0x10000000020a56f5dd13b96dd4f5338))))) (N (N (N (L 0x1000000001fc68b895b5ef579bbdbb2) (N (L 0x1000000001a3362e3405fb906d03334) (L 0x100000000172ee1c70791ffdedc3895))) (N (L 0x10000000011ff16627d2531ba247417) (N (L 0x1000000000eb266f0b4181f231579ff) (L 0x1000000000accf6af50d6f453974135)))) (N (N (L 0x100000000083b68bb8c4a1e8c9d328d) (N (L 0x10000000005c10eaaddc0a8a934b3c2) (L 0x1000000000420cc016a2fc2dfa321fa))) (N (L 0x10000000002c16b009f343e94da3d78) (N (L 0x10000000001df8b78946602cb153def) (L 0x1000000000132bca8b046508a8d5d70)))))) (N (N (N (N (L 0x10000000000c6a683acf65e71e9f0a7) (N (L 0x100000000007a207493e36584becb1e) (L 0x100000000004bae4845bb5dee55035c))) (N (L 0x100000000002cd63034b1a07db4550f) (N (L 0x100000000001aaf209ffae1b536399e) (L 0x100000000000f4514d5dcf5eb846b1f)))) (N (N (L 0x1000000000008c1398d8f04e5abe98d) (N (L 0x1000000000004d95c8f6eafe82f8b39) (L 0x1000000000002af78a216591981ce3b))) (N (L 0x1000000000001713b429f06b2470f7b) (N (L 0x1000000000000c5f8507b56b32168e0) (L 0x1000000000000674659b6cc8e8c3857))))) (N (N (N (L 0x100000000000035b791e0fef69a47af) (N (L 0x10000000000001b42454605d046eb97) (L 0x10000000000000dc7618d1fc6837c26))) (N (L 0x100000000000006cf8ff812f8324bb4) (N (L 0x10000000000000359d9d65a7d773bad) (L 0x1000000000000019d8b8eff19b162c8)))) (N (N (L 0x100000000000000c6533933c8dc9884) (N (L 0x1000000000000005d5916c6211cb1f8) (L 0x1000000000000002bb0d3a9659b742d))) (N (L 0x100000000000000141970bd9eababb0) (N (L 0x10000000000000009310f2e1a4919ac) (L 0x10000000000000004230626cb83645d))))))) (N (N (N (N (N (L 0x10000000000000001d9b066cb95c369) (N (L 0x10000000000000000d0c02975a6056d) (L 0x100000000000000005b6988f39cae77))) (N (L 0x10000000000000000277a55a58748f5) (N (L 0x1000000000000000010f07935d22673) (L 0x10000000000000000072ca908b8c7d0)))) (N (N (L 0x100000000000000000304d52d14279b) (N (L 0x1000000000000000001413ca95269df) (L 0x100000000000000000084a71bb9eca4))) (N (L 0x1000000000000000000362615dc9a24) (N (L 0x100000000000000000015f579bc170a) (L 0x100000000000000000008cedd9ca4b9))))) (N (N (N (L 0x1000000000000000000038290662926) (N (L 0x1000000000000000000016260acce6e) (L 0x1000000000000000000008ada9800c7))) (N (L 0x10000000000000000000035deff019b) (N (L 0x10000000000000000000014c4110c4f) (L 0x10000000000000000000007edf63ade)))) (N (N (L 0x1000000000000000000000302362ab9) (N (L 0x10000000000000000000001219c394d) (L 0x100000000000000000000006c362d26))) (N (L 0x100000000000000000000002815b17a) (N (L 0x100000000000000000000000ec19697) (L 0x1000000000000000000000005632129)))))) (N (N (N (N (L 0x1000000000000000000000001f467ec) (N (L 0x1000000000000000000000000b41fd2) (L 0x10000000000000000000000004071d7))) (N (L 0x100000000000000000000000016e15a) (N (L 0x100000000000000000000000008132f) (L 0x100000000000000000000000002d428)))) (N (N (L 0x100000000000000000000000000fc31) (N (L 0x1000000000000000000000000005732) (L 0x1000000000000000000000000001df9))) (N (L 0x1000000000000000000000000000a3b) (N (L 0x1000000000000000000000000000379) (L 0x100000000000000000000000000012a))))) (N (N (N (L 0x1000000000000000000000000000064) (N (L 0x1000000000000000000000000000020) (L 0x100000000000000000000000000000a))) (N (L 0x1000000000000000000000000000003) (N (L 0x1000000000000000000000000000001) (zL)))) (N (N (zL) (N (zL) (zL))) (N (zL) (N (zL) (zL)))))))

private def cpos_lf_231 : FastDTree := dleaf cpos_bt_231 0xffffffffff95ab8a93b30cbfb4728e 0x1000000000077aa08fe109197b2dae8 0xfffffffffff7b552eef08f1169c755 0x100000000002c00ff23ce84c8877f9d 0xa01473764999d07d1e82 0x2cc73e15a952fd796536 (M 0xffffffffff92324876d5c81479709f 0x1000000000068b1ffe4fb26dbadb97a 0xfffffffffff4ddcebc491f65d24dcb 0x100000000002a787dce212bf507bfec 0x100000000002a5a87ce215f992f922e 0x10000000000e85e7b58662d943f647d 0x10000000000c7e614559a922d3360b8 0x1000000000074adb83e3ef94cd4636b 0x2be7dee6cfeff3ee370f (Q 0x97b7752ca7e972c6163a 0xec3289877b36b73dfda9 0xe775946da27347df7090)) (M 0xffffffffff8fb1f8d2635427add17b 0x100000000004d8511eb7f0e49f2a5f2 0xffffffffffefe44d84c69160e06dc7 0x1000000000026db7fb6459b8f76b6ca 0x10000000000002275f5fc5cf97d19a9 0x10000000000ca334f7e1ab5f221f844 0x100000000008c9405c1502ae805c1de 0x100000000007a8a22b362f2520a8e40 0x2a105ce80e5e68685c68 (Q 0x88761861e24faa27227a 0xca3352ade7b60f217a7f 0xba7d36345afd2c00e6d2)) (M 0xffffffffff919fdd0845b6d37a143e 0x1000000000036263bceb35e36d37633 0xffffffffffebe4d4b795d58b595091 0x1000000000022bbbc09a20a9526bf20 0xffffffffffe2ddc49ac1b178eb950f 0x10000000000abe1dd46b1c5d3e46b1d 0x100000000005fa9e6c5209487b7014f 0x1000000000076e1d479237f1896b596 0x28220f7eaa81b565a7ca (Q 0x7af155eeb0e4094d1c46 0xae5577bf098dffcd06b3 0x9897b596e9b259d3c354)) (M 0xffffffffff96926747c77e38f172e6 0x10000000000227b38f2ac208694d5aa 0xffffffffffe8db5eaf48c384bf03a8 0x100000000001e557821241fe59a4af3 0xffffffffffcf625d6b654fa4c24d9e 0x100000000008f2a7cfdfc9e01b74b9b 0x100000000003dcc832db0c3bd7e425b 0x100000000006e4842533ac80f838497 0x26277c672cbeec00584a (Q 0x6eec72a43cb709b716a0 0x9731f8a9cb24d755c1c6 0x7e6ac630123916e36bf1))

private def cpos_bt_233 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0x100000000020fc99de997d92f16a811) (L 0x10000000006a00fdb788cb47e28b05b))) (N (L 0x1000000000abcefa6e40d558ab33686) (N (L 0x1000000001470fd41e870380f85390d) (L 0x1000000001bc1d31be5cc7c91bfe4ca)))) (N (N (L 0x100000000283320de42359476c1781c) (N (L 0x1000000002f870c39ec5c97b0d460d9) (L 0x1000000003979130aab714147eba446))) (N (L 0x1000000003cb16ff8e147e76c726e64) (N (L 0x100000000403d12f6a608307800ef9b) (L 0x1000000003db2a8d9f764095f84eb7a))))) (N (N (N (L 0x1000000003ac76ba22a49d4765ff2f4) (N (L 0x1000000003409228b3a8f43815b78b3) (L 0x1000000002d730a6f3c7cd67ed29335))) (N (L 0x1000000002577dafb7bff440865016f) (N (L 0x1000000001e64a9bec75b66885c92a1) (L 0x1000000001785a388760db0a6c19401)))) (N (N (L 0x10000000011e4088b4383a7a8b6257f) (N (L 0x1000000000d15547209b1f40217f362) (L 0x10000000009664693df67840ccf0f31))) (N (L 0x1000000000687a9a35b027da8af199a) (N (L 0x10000000004750a73e2c18fe6d3a303) (L 0x10000000002f468c74bd8892b270c72)))))) (N (N (N (N (L 0x10000000001ecde3a965ebc09edeb3e) (N (L 0x1000000000138f3ddb6165682999d00) (L 0x10000000000c36c7b95d26d7ddebd5d))) (N (L 0x10000000000773d5f0e8f15dd6ee284) (N (L 0x1000000000047983321baeb20c7e849) (L 0x100000000002a18617f6c6d63e296b1)))) (N (N (L 0x10000000000185f09bbc28c94ee53d5) (N (L 0x100000000000dd78e960c60877b37ad) (L 0x1000000000007bf07e74c10a2d4c4df))) (N (L 0x100000000000442506f07d8650dcab3) (N (L 0x10000000000024f08a12ccc3794766f) (L 0x10000000000013b2e67781d0a413e2f))))) (N (N (N (L 0x1000000000000a5cef4c30c5a36f8da) (N (L 0x100000000000055e79a05f1c005ccab) (L 0x10000000000002bee5e8bde7e0fe5b2))) (N (L 0x1000000000000162581703aae83fd16) (N (L 0x10000000000000b06a63cb7a66f9a99) (L 0x1000000000000056a76269a53bd05d2)))) (N (N (L 0x100000000000002a0e944cec5a50c45) (N (L 0x1000000000000014273f1435191f475) (L 0x10000000000000098bff4a7f6136182))) (N (L 0x100000000000000477d21cc878dd949) (N (L 0x100000000000000211702c7654fd0d1) (L 0x1000000000000000f240e437bcb9840))))))) (N (N (N (N (N (L 0x10000000000000006dacbfac8964b69) (N (L 0x1000000000000000311c2f1e6f712a0) (L 0x100000000000000015c4356e02f35aa))) (N (L 0x1000000000000000098be07125cc3c7) (N (L 0x1000000000000000042550792ffa340) (L 0x100000000000000001c8484fac3956b)))) (N (N (L 0x100000000000000000c24e610de6528) (N (L 0x10000000000000000051f2ad0f1cdbc) (L 0x100000000000000000223ea6f61a039))) (N (L 0x1000000000000000000e2d8260cbe60) (N (L 0x10000000000000000005d15b751363f) (L 0x100000000000000000025db2894cc34))))) (N (N (N (L 0x10000000000000000000f4374faf79a) (N (L 0x10000000000000000000619e8235c2d) (L 0x1000000000000000000026b2630bed3))) (N (L 0x100000000000000000000f3642277d7) (N (L 0x1000000000000000000005ee88a25ae) (L 0x10000000000000000000024b5eafafa)))) (N (N (L 0x1000000000000000000000e16bb347d) (N (L 0x100000000000000000000055d63ebe6) (L 0x1000000000000000000000207003924))) (N (L 0x10000000000000000000000c2a52e60) (N (L 0x100000000000000000000004876222c) (L 0x100000000000000000000001ac706cd)))))) (N (N (N (N (L 0x1000000000000000000000009d30e3d) (N (L 0x1000000000000000000000003942bac) (L 0x10000000000000000000000014b68f6))) (N (L 0x1000000000000000000000000770cf2) (N (L 0x10000000000000000000000002a79b5) (L 0x10000000000000000000000000f0d61)))) (N (N (L 0x1000000000000000000000000054c81) (N (L 0x100000000000000000000000001da64) (L 0x100000000000000000000000000a4d4))) (N (L 0x10000000000000000000000000038e7) (N (L 0x1000000000000000000000000001385) (L 0x10000000000000000000000000006a7))))) (N (N (N (L 0x1000000000000000000000000000240) (N (L 0x10000000000000000000000000000c1) (L 0x1000000000000000000000000000040))) (N (L 0x1000000000000000000000000000014) (N (L 0x1000000000000000000000000000006) (L 0x1000000000000000000000000000002)))) (N (N (zL) (N (zL) (zL))) (N (zL) (N (zL) (zL)))))))

private def cpos_lf_233 : FastDTree := dleaf cpos_bt_233 0xffffffffff7bfeb11888a42302c661 0x100000000006fdd50c040d2b5be33f1 0xffffffffffedd7f12bdbe7853cf512 0x100000000002ab58e80d9aa857c3a66 0xad07691844d9e89a5f84 0x2e688932c09d2ddba618 (M 0xffffffffff799367e8d69c72927b9d 0x100000000005f4225dcea6df75952db 0xffffffffffeb252a76725e02ca6641 0x1000000000028aa24a347685024aabf 0x10000000000188cfbeb7d3c56b36430 0x100000000010165df6bd9a3b503446b 0x10000000000d5de704b3ca04a042745 0x10000000000879dce64e608e62ab36c 0x2db353cce7a875f3989e (Q 0xa4c1234a2e59712a2d90 0x10290ed6659613c4c9ca5 0xfd3e0f8cf0fb58444936)) (M 0xffffffffff797d99b98230bbd25b7a 0x1000000000041416cd5d371b1ea87b6 0xffffffffffe68e82693f14e9525344 0x100000000002415577795179454dfd6 0xffffffffffeb7f49cc3e2614f7b6b0 0x10000000000de615d25b28398bf050e 0x10000000000955cd1d8cb4465275c1f 0x100000000008e29ae4f34ef5afb7676 0x2c26d5ac7941ad6cd52b (Q 0x9580b1f95f868716ee5d 0xdf52cf78683646d8e953 0xce33d35dc23ea0ea4d2b)) (M 0xffffffffff7e1cadbf9ad88190428c 0x1000000000027aafaf0aefbcb6117d6 0xffffffffffe30faf3e7fae1b308d2b 0x100000000001f144f6b48baff0c07ca 0xffffffffffcc9ee2566d828a64a243 0x10000000000bb331eb295046cf17481 0x1000000000063dd00447be53dfb721d 0x1000000000089fd2be1b05ddf93c6ce 0x2a77571f2ddfc3e93a33 (Q 0x87cf6daa5efb706547ff 0xc21f5f3b91e375eb6349 0xaa5578ab2967b7c627f5)) (M 0xffffffffff85e283cf79b6cf246228 0x100000000001260a6f3df95c82871b3 0xffffffffffe09f607fbdc05916e8f6 0x1000000000019e6dc86c33b747a6e1f 0xffffffffffb89548d90eb922bc5bff 0x1000000000099dce570567cc3428c95 0x100000000003e2d313a5ec6c6d3bcef 0x100000000008006b76e2a89909c98f0 0x28afeb773ffb39079a70 (Q 0x7b7d839c1c8722625294 0xa9a1244fa662c4e88ef0 0x8e53692024ee4df30f8f))

private def cpos_bt_235 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0x10000000002a69581e330f2aa41b384) (L 0x10000000008035e21a7edd18ca14d54))) (N (L 0x1000000000f0848f6e800ecab5a0a08) (N (L 0x1000000001bfdc1f7f3603129033fac) (L 0x10000000029e5cb754a00f4ea3e8e9a)))) (N (N (L 0x1000000003c7f25c2ee52c65ccdaf12) (N (L 0x1000000004cc6e3b0a849a275868d39) (L 0x1000000005d7f7d32e4067d93108504))) (N (L 0x1000000006850790c4f3ca54c7b080a) (N (L 0x1000000006fcc8b839ea790d2e94191) (L 0x1000000007049ef1059e83592ac690f))))) (N (N (N (L 0x1000000006ca730e5e94053f88b9082) (N (L 0x10000000063e496bb666a4638838077) (L 0x10000000058c3086e019830a6fdbe4c))) (N (L 0x1000000004b9f0b6e53ad23732585fb) (N (L 0x1000000003e74eae14286c314e7875e) (L 0x10000000031c5f8dd17c929e99792a6)))) (N (N (L 0x100000000268ede78ded3a89916b24a) (N (L 0x1000000001cf4c55a31323933345226) (L 0x1000000001530598107c344a034330f))) (N (L 0x1000000000f1596b82d5ad1e8f025e3) (N (L 0x1000000000a7c52ff236a8d493bb3cb) (L 0x100000000071c6bd31ca206acecc403)))))) (N (N (N (N (L 0x10000000004b7ae51fd59089ff7933c) (N (L 0x100000000030f668936d721b3dfe85c) (L 0x10000000001f1e9620e6db97852cc62))) (N (L 0x1000000000136041039b7496219d476) (N (L 0x10000000000bd644b8a67a0d592a10f) (L 0x100000000007185e3c72879d1ee9b83)))) (N (N (L 0x1000000000042d91e5254663106fe0e) (N (L 0x1000000000026ac9d80c4f20d36c899) (L 0x1000000000016012e80f7d7afdfcf40))) (N (L 0x100000000000c50a6ecedfd574d5e8e) (N (L 0x1000000000006c8eca44342067a93d9) (L 0x1000000000003ae3a4518ec98138d3d))))) (N (N (N (L 0x1000000000001f79bbb8987dc5311bf) (N (L 0x10000000000010944fff03145d997b8) (L 0x100000000000089c79cab43c986794f))) (N (L 0x100000000000046949e5857b783d553) (N (L 0x100000000000023ad7bbe1378dcd277) (L 0x100000000000011ccc6f2eab9317024)))) (N (N (L 0x100000000000008c4c39117401e1b89) (N (L 0x100000000000004441f2672bfe7111b) (L 0x1000000000000020cf319ade590e0ae))) (N (L 0x100000000000000f958af050389ad82) (N (L 0x1000000000000007513718449691d77) (L 0x10000000000000036599e1342b43754))))))) (N (N (N (N (N (L 0x10000000000000018f4006adff06c83) (N (L 0x1000000000000000b5521316c58aaa2) (L 0x1000000000000000517a451bda6a288))) (N (L 0x1000000000000000243b87ed9ae3b85) (N (L 0x10000000000000000ff2e8a2811fc22) (L 0x100000000000000006f34a7d511471d)))) (N (N (L 0x100000000000000002ffd355eaea1f1) (N (L 0x100000000000000001482976daa69ad) (L 0x1000000000000000008aef0ff0c7648))) (N (L 0x1000000000000000003a46a83cccbda) (N (L 0x1000000000000000001838d7106f906) (L 0x10000000000000000009fa50b24e45d))))) (N (N (N (L 0x1000000000000000000412f8e25a13f) (N (L 0x10000000000000000001a6301b6a077) (L 0x10000000000000000000a972ffb5962))) (N (L 0x1000000000000000000043712eb23e4) (N (L 0x100000000000000000001a9f4088999) (L 0x100000000000000000000a6c7dde096)))) (N (N (L 0x10000000000000000000040c868deb2) (N (L 0x10000000000000000000018f764e5d4) (L 0x100000000000000000000098c23ac14))) (N (L 0x100000000000000000000039f8dffde) (N (L 0x100000000000000000000015d5ede77) (L 0x10000000000000000000000829eeb66)))))) (N (N (N (N (L 0x10000000000000000000000307aee32) (N (L 0x1000000000000000000000011dd4332) (L 0x100000000000000000000000689410f))) (N (L 0x10000000000000000000000025fedde) (N (L 0x1000000000000000000000000db5a0f) (L 0x10000000000000000000000004e9b9a)))) (N (N (L 0x10000000000000000000000001bfb2f) (N (L 0x100000000000000000000000009e4e8) (L 0x10000000000000000000000000379c7))) (N (L 0x100000000000000000000000001368d) (N (L 0x1000000000000000000000000006bb1) (L 0x100000000000000000000000000251c))))) (N (N (N (L 0x1000000000000000000000000000cb4) (N (L 0x1000000000000000000000000000452) (L 0x1000000000000000000000000000176))) (N (L 0x100000000000000000000000000007d) (N (L 0x1000000000000000000000000000029) (L 0x100000000000000000000000000000d)))) (N (N (L 0x1000000000000000000000000000004) (N (L 0x1000000000000000000000000000001) (zL))) (N (zL) (N (zL) (zL)))))))

private def cpos_lf_235 : FastDTree := dleaf cpos_bt_235 0xffffffffff63e24434b859f123e2c2 0x100000000006267113d18f8718b002e 0xffffffffffe4a15e5544562e5c65e0 0x1000000000026bab4dcb9d32d080dfd 0xb88a749ecf31222ce6a7 0x2f6c9b3b0edf37b9809f (M 0xffffffffff62d0100094b7bcec3800 0x100000000005046bcbafa4cab97eb04 0xffffffffffe22f4e54e2948cb16827 0x100000000002434670bb4a686eadaef 0x100000000000225526887b2310ab203 0x10000000001186561a1c1cd46cb0f95 0x10000000000e24bc99362c0a8ecbb35 0x100000000009d05272e68d92f1ea54b 0x2ee6b8704b081922aaa3 (Q 0xb07fe84be11055bf74bf 0x118677bf6573621285f53 0x1136fb97b376da6ae1128)) (M 0xffffffffff65b160457796b71d3dc1 0x100000000002fbc94b570eb5d57cfba 0xffffffffffde31818821e801a95e1e 0x100000000001ebc5f7d9eea8c5a0e68 0xffffffffffd2b00047145e795c164b 0x10000000000eff599523b47b980d5f8 0x100000000009c44aa4156bbf1943983 0x10000000000a3df5257e15f9cb402e4 0x2db0a616bcf5f8836803 (Q 0xa185ba56f9269c500925 0xf4333e7ab1d47c49b512 0xe26ffb08ba0d7505cc5a)) (M 0xffffffffff6d7f49fb6a703bdb8c52 0x1000000000014498d80c034f7168071 0xffffffffffdb661cbb6fcf3427a929 0x1000000000018f44a6431f1fcbc21fd 0xffffffffffb2b44d28f9c8cbbd1558 0x10000000000c7723d6aa9273711661a 0x1000000000065f1db99dd6c5ebdda78 0x100000000009ec3e5481590fdbe32ae 0x2c4c6b0cf1210ea0a631 (Q 0x93e69967d8b5512e0cd9 0xd5e688a2b88193551b4b 0xbcad649b2d10fd2b1fd4)) (M 0xffffffffff78853011c1c6b841cddd 0xfffffffffffdc847ad273526ade776 0xffffffffffd9bdd949eb591344d3a6 0x10000000000131ee8dd5a71a55c74b5 0xffffffffff9ea92d85e655472e6baa 0x10000000000a120138baf024da22f83 0x100000000003c4ab083470f0d6d9514 0x1000000000093026f676be248aadfc6 0x2ac53a0dfc7342074a2f (Q 0x877f759aa058086519bd 0xbc3ec89e66866daf2ae4 0x9ee488d15a46dfdc7122))

private def cpos_bt_237 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0x100000000033d6165dcca0c256cbef7) (L 0x10000000009bf7ff9632735deb8118a))) (N (L 0x100000000143f167a997aa2cfe9de30) (N (L 0x1000000002654dfe15779e6c60f0ade) (L 0x1000000003d47d8244c4c24713b24e2)))) (N (N (L 0x1000000005a9623be1e6a605522770e) (N (L 0x10000000078b7096c08f9d32876cbfb) (L 0x10000000096cbbd129a00f54f9e7fc6))) (N (L 0x100000000aeff6295d906bc4cdbb527) (N (L 0x100000000c06952d47868a1fc8218da) (L 0x100000000c7d9858ac7109309e9bbd3))))) (N (N (N (L 0x100000000c6439ca79e2fc9286cb585) (N (L 0x100000000bbc477973784a4b2d364d1) (L 0x100000000aae839ceeded49599a57ab))) (N (L 0x1000000009592e1f7aa2fef2093292a) (N (L 0x1000000007e6bf9630f1ba2fb5779c0) (L 0x100000000674764cb67c54ea2d13444)))) (N (N (L 0x10000000051ccbc806cc30f7f79ad06) (N (L 0x1000000003ede9d16db3efc561a70ec) (L 0x1000000002efe78ba9edec30f69bae9))) (N (L 0x1000000002231b02f459c0a33532b52) (N (L 0x1000000001842a4c0577884ea4ae362) (L 0x10000000010cc2f22422cf4aaf66df0)))))) (N (N (N (N (L 0x1000000000b5d797a14739818fa37fc) (N (L 0x10000000007851b6bbc0d38a61bd9f0) (L 0x10000000004df01ac75ffeb0aae75e0))) (N (L 0x100000000031755191213b53aaf0df3) (N (L 0x10000000001ec62ab041c56f7a0f304) (L 0x100000000012c97e3210377debbaf58)))) (N (N (L 0x10000000000b42d685c3ce7eacffa3e) (N (L 0x100000000006a195f9cf4fe4d6b2301) (L 0x100000000003d6aa99d9141fde07813))) (N (L 0x1000000000022f737527d84877f7427) (N (L 0x100000000001396d17a86ac8384e741) (L 0x100000000000acdefd5835722a3d201))))) (N (N (N (L 0x1000000000005de9efaeedf5bd2ceba) (N (L 0x1000000000003245deb5c4e878cedb3) (L 0x1000000000001a8763c8edc862fa1c1))) (N (L 0x1000000000000dce23234cbe29cc8db) (N (L 0x10000000000007164ea947cbcb7b08b) (L 0x100000000000039726849fcecdb0a2e)))) (N (N (L 0x10000000000001cbae51944219f28c1) (N (L 0x10000000000000e303a6f891efa81f1) (L 0x100000000000006ebdaeec5bb39219e))) (N (L 0x100000000000003560293f4acedbece) (N (L 0x10000000000000196d0a50fecb973e7) (L 0x100000000000000bf937b419ff7b3db))))))) (N (N (N (N (N (L 0x10000000000000059355179a50fe080) (N (L 0x1000000000000002915eff9f795e3c1) (L 0x10000000000000012b83b0f9b0f4392))) (N (L 0x10000000000000008708847c6038e5a) (N (L 0x10000000000000003c4085cd98a4c8a) (L 0x10000000000000001a9cfdb3232b75d)))) (N (N (L 0x10000000000000000ba380ff4e23e34) (N (L 0x1000000000000000050a5c3f5a57f29) (L 0x100000000000000002298002e152be9))) (N (L 0x100000000000000000eb3371d8ade45) (N (L 0x10000000000000000063069b45271d6) (L 0x1000000000000000002950d4ebbe751))))) (N (N (N (L 0x1000000000000000001115b2eaa651d) (N (L 0x1000000000000000000700ceb3287b1) (L 0x10000000000000000002d892ddb4659))) (N (L 0x10000000000000000001259508798d7) (N (L 0x1000000000000000000075513468499) (L 0x100000000000000000002e7f4a6c0ad)))) (N (N (L 0x100000000000000000001247bd094d7) (N (L 0x1000000000000000000007213cad7ed) (L 0x1000000000000000000002c2568c3b7))) (N (L 0x10000000000000000000010f3d3bbb0) (N (L 0x1000000000000000000000675e55a33) (L 0x1000000000000000000000271964a15)))))) (N (N (N (N (L 0x10000000000000000000000eae2ea2c) (N (L 0x10000000000000000000000578d3055) (L 0x1000000000000000000000020667bad))) (N (L 0x100000000000000000000000be7e0eb) (N (L 0x1000000000000000000000004582aff) (L 0x1000000000000000000000001930a36)))) (N (N (L 0x1000000000000000000000000911148) (N (L 0x100000000000000000000000033dd77) (L 0x1000000000000000000000000126ba3))) (N (L 0x1000000000000000000000000067fe2) (N (L 0x100000000000000000000000002474e) (L 0x100000000000000000000000000cb2f))))) (N (N (N (L 0x1000000000000000000000000004655) (N (L 0x1000000000000000000000000001831) (L 0x1000000000000000000000000000845))) (N (L 0x10000000000000000000000000002ce) (N (L 0x10000000000000000000000000000f2) (L 0x1000000000000000000000000000050)))) (N (N (L 0x100000000000000000000000000001a) (N (L 0x1000000000000000000000000000007) (L 0x1000000000000000000000000000002))) (N (zL) (N (zL) (zL)))))))

private def cpos_lf_237 : FastDTree := dleaf cpos_bt_237 0xffffffffff4ed3030aca024721d44f 0x100000000004fe8f76d7968933c140e 0xffffffffffdce2abc436694c48d399 0x10000000000206f31cdeccfc9bc5e28 0xc25cd891d9fb54dac1e9 0x2fcd489a52b2578da265 (M 0xffffffffff4f5e30b6409bfd7b8395 0x100000000003c712e08fffed51a591e 0xffffffffffdaca6f684d89b28f8e44 0x100000000001d7cf5031f56c6df9b61 0xffffffffffe797842c362fb981d9d2 0x100000000012c64b7fe66ffbc8e4a04 0x10000000000ecbf499d9eaef5e1b5a7 0x10000000000b4a947b20d061f8b5dc9 0x2f7a2463d8cf5f5a3817 (Q 0xbaaff12c74a510353000 0x12d6228b46cf309dc37c4 0x129ce0b60904930912e8a)) (M 0xffffffffff55b30f88636a723b8eff 0x1000000000019c5ff1323fe07868476 0xffffffffffd794d4db526ab872015c 0x100000000001743b5bdb347022d11ab 0xffffffffffb642fc9ab06b453f0bf9 0x10000000000fe08233cadf4650774dc 0x10000000000a0e76cfa9969226c438a 0x10000000000bb62992af19276fca3cb 0x2ea2c70cc628168ac45c (Q 0xac3d630f428136c3106d 0x108847918d3a8bf282d23 0xf6fd0b4f391e5e0eb10e)) (M 0xffffffffff611a2816394d11414295 0xfffffffffffced32d8a8088273f498 0xffffffffffd5a7cacc0a10ef0ad8a2 0x1000000000010db8238a1672be2a398 0xffffffffff95c3e72e3f008754c1fa 0x10000000000cfcafa6d1e5faa48c80a 0x100000000006590e8825c7840ee83b1 0x10000000000b4e1cd655701f31ce6c8 0x2d93a30ab1d73b9c5282 (Q 0x9eed73f4b41d8a6cccfe 0xe95fe654b9d4d93a9692 0xcf724231e104a5408d0f)) (M 0xffffffffff6fb6da179b987de98c17 0xffffffffffe5b68454850a76e0880f 0xffffffffffd4ed829513395e57b048 0x100000000000a8952ccaacf3dd0b261 0xffffffffff825819c364de878dd1b8 0x10000000000a4360b86b04e6395ec10 0x1000000000037db5e9ccdb14f4c7c9f 0x10000000000a6ddf017286e4095a616 0x2c579c47eb20372572af (Q 0x92a9289b769018fb1caf 0xcec5a5f7db32e5cf324a 0xaff7b06affde913234de))

private def cpos_bt_239 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0x100000000041f933bd32fb25e2d5023) (L 0x1000000000d003f6de232d1f8a2c170))) (N (L 0x1000000001e3d398f7d66c45e35fa69) (N (L 0x1000000003c6c7bd319556e5bbe5dac) (L 0x100000000684291c01049d97a42bf03)))) (N (N (L 0x100000000a2491bf1930cce38e4fdbd) (N (L 0x100000000e5a4891dd79b94743f6f4f) (L 0x1000000012ceee3f6a8040a2f39e102))) (N (L 0x1000000016f83d21cb2c79fc8e0632e) (N (L 0x100000001a660f683a37e5fe8145947) (L 0x100000001cb05b7efbcfb89a57904cd))))) (N (N (N (L 0x100000001da826f999c8baf8d0e6149) (N (L 0x100000001d44a25a01937a425ddeca5) (L 0x100000001baf6ea640557c4b4b88f04))) (N (L 0x10000000192bd7175555d621d4dde21) (N (L 0x10000000160f5094fcc795b868c0a11) (L 0x1000000012ad32a378545c3382ae695)))) (N (N (L 0x100000000f4ee85fe3099fd4b3e81ea) (N (L 0x100000000c2b40470895bd5801fd33c) (L 0x100000000965c53f481c9ed501324e0))) (N (L 0x10000000070f7ac31f3b667160841b4) (N (L 0x10000000052af1e4fa98bccde4a9f24) (L 0x1000000003b072496d1ad9e358c66c2)))))) (N (N (N (N (L 0x1000000002925da252914af85b74b20) (N (L 0x1000000001c0965d37531f9ab156948) (L 0x10000000012b098d7865e20e3e28bf1))) (N (L 0x1000000000c3326e4573dcfff73c5fa) (N (L 0x10000000007cdd409daba17664afb3b) (L 0x10000000004e550457e512cc8883d80)))) (N (N (L 0x10000000003039c195e6184e792fbaf) (N (L 0x10000000001d27f6fa4ac7b3f92b382) (L 0x10000000001152022ecd305cc0105b7))) (N (L 0x10000000000a1da7a2646b3796a97a3) (N (L 0x100000000005cfc48e1d41d94f2504a) (L 0x100000000003492f4c056a9a26352e6))))) (N (N (N (L 0x100000000001d449f6c780de8dd2857) (N (L 0x10000000000100cca4c267adfe40257) (L 0x1000000000008ac68b9e7b590b30c65))) (N (L 0x10000000000049ef0573e6e6937ea14) (N (L 0x10000000000026d88956dace9ec6ff4) (L 0x1000000000001422d3ab9506aaddbfb)))) (N (N (L 0x1000000000000a4d0bc9922bc36f207) (N (L 0x1000000000000533c9b423741c8110a) (L 0x1000000000000298335eb7989520dae))) (N (L 0x100000000000014737d8626b4523f21) (N (L 0x100000000000009f488ed78b3b7fc47) (L 0x100000000000004ca20146e05eb9e08))))))) (N (N (N (N (N (L 0x100000000000002472d93ecc1d8be2b) (N (L 0x1000000000000011247f0148f602b32) (L 0x1000000000000007f975405beb867c0))) (N (L 0x1000000000000003ab7df2bab25bff8) (N (L 0x1000000000000001abd38810cf52837) (L 0x1000000000000000c0d21e94842a04e)))) (N (N (L 0x100000000000000056071f4d6a25ed2) (N (L 0x1000000000000000260081e159a9d78) (L 0x1000000000000000109fc0378223184))) (N (L 0x10000000000000000733f02b7cea870) (N (L 0x1000000000000000031776eae83b945) (L 0x1000000000000000015097859f47a19))))) (N (N (N (L 0x1000000000000000008dd9df0eee2bc) (N (L 0x1000000000000000003b3fe771ba2ef) (L 0x10000000000000000018881e07b7fc9))) (N (L 0x1000000000000000000a11e04bc7f3c) (N (L 0x10000000000000000004193a10eff6d) (L 0x10000000000000000001a77ed64466f)))) (N (N (L 0x10000000000000000000a988c16d941) (N (L 0x1000000000000000000043522c65f6f) (L 0x100000000000000000001a85409d234))) (N (L 0x100000000000000000000a5da6ce33b) (N (L 0x10000000000000000000040537842f4) (L 0x10000000000000000000018c267e190)))))) (N (N (N (N (L 0x10000000000000000000009756cea38) (N (L 0x1000000000000000000000396382808) (L 0x1000000000000000000000159a96006))) (N (L 0x100000000000000000000008130a7ff) (N (L 0x100000000000000000000002ff1583b) (L 0x1000000000000000000000011aadf07)))) (N (N (L 0x1000000000000000000000006773fcc) (N (L 0x100000000000000000000000259a87d) (L 0x1000000000000000000000000d939de))) (N (L 0x10000000000000000000000004de8ad) (N (L 0x10000000000000000000000001bc26e) (L 0x100000000000000000000000009d3b5))))) (N (N (N (L 0x10000000000000000000000000374e4) (N (L 0x100000000000000000000000001354b) (L 0x1000000000000000000000000006b6e))) (N (L 0x1000000000000000000000000002515) (N (L 0x1000000000000000000000000000cb8) (L 0x1000000000000000000000000000455)))) (N (N (L 0x1000000000000000000000000000177) (N (L 0x100000000000000000000000000007d) (L 0x1000000000000000000000000000029))) (N (L 0x100000000000000000000000000000d) (N (L 0x1000000000000000000000000000003) (L 0x1000000000000000000000000000001)))))))

private def cpos_lf_239 : FastDTree := dleaf cpos_bt_239 0xffffffffff3771de43ced09369e480 0x100000000002d23330fa1f156422ba2 0xffffffffffd54c2502ded7777b5f05 0x100000000001411d39e51de96707fa8 0xcd92640a8a6a94029539 0x2f2f0577a81f87b4c750 (M 0xffffffffff3ad137d18227223ee02e 0x10000000000181a8d9f2de0230b46c6 0xffffffffffd3defdc137c18bcadc81 0x1000000000010a5df28e50498d351ec 0xffffffffffb987fa289378fc11aaad 0x100000000014304784f650a0bffde84 0x10000000000f7e89edbbb0c1419a579 0x10000000000db9b1b4e5e4396c64e2b 0x2f2a2fd565d8aa756536 (Z (Q 0xc341dc5d9d97a0ce1755 0x14104177fed57ba6ef4bc 0x14b301d9429abd90baeea) (S (Q 0xc85cf5125aedfabc124c 0x14fca3d655bb5b406a61f 0x14b301d9429abd90baeea) (S (Q 0xcaf7f6d99eab72e96874 0x157fdaf6475f4c04782b6 0x14b301d9429abd90baeea) (S (Q 0xcc4b1ea3e56e681889ea 0x15c475061fe94c4c053d2 0x14b301d9429abd90baeea) (Q 0xcd2fc739a9b3c155049e 0x15f3405e8558cc0beacc4 0x14b301d9429abd90baeea)))))) (M 0xffffffffff470810b793cbe481479d 0xfffffffffff336778ce471add30466 0xffffffffffd2173c59c36bf237d11b 0x1000000000009a154fefc8563155b22 0xffffffffff8694aee27650306dde36 0x100000000010b02c4a53a028a442a80 0x10000000000a2e7fdc84237983ff43c 0x10000000000e138cf1ba6275bcc9f66 0x2ee88db2b657862ce09b (Q 0xb968f42aa79691145136 0x12552427efe14971473bd 0x115f67d7737971a254f3b)) (M 0xffffffffff58621aa8fca5f1700ef6 0xffffffffffd5522c1d03d038a94649 0xffffffffffd1aeeb89055cc1f2b0db 0x1000000000002a67c91f4249d94fa67 0xffffffffff6695d52bcdab689d9a26 0x10000000000d3a8da212f9d6dcb5d05 0x100000000005fd14b1074ee96ad6325 0x10000000000d7ad8bb690c7d3acae0e 0x2e647a30e9a2a47970fa (Q 0xacf70911b9283c5a43ce 0x10569495b49d70bca0bc0 0xec01113800e88ca8bf9f)) (M 0xffffffffff6cc4d9c9d1ff806ae85f 0xffffffffffbe2582d55592ce22cfc1 0xffffffffffd285a7126ef11828441d 0xfffffffffffbfc0c8323b3cacf53d6 0xffffffffff5566988ce5bddad47dc9 0x100000000009fe60595d696fbb7879a 0x100000000002bfdec42a8802479017e 0x10000000000c557e0c84493aebb02ba 0x2da7a43072c71054560e (Q 0xa1499ae72bdb8f6c14ea 0xe9d1d60576b066dfce7f 0xca2feaff139e895bba3c))

private def cpos_sub_27 : FastDTree := (dsplit (dsplit (dsplit cpos_lf_227 cpos_lf_229) (dsplit cpos_lf_231 cpos_lf_233)) (dsplit (dsplit cpos_lf_235 cpos_lf_237) cpos_lf_239))

private def cpos_bt_242 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0x100000000054d2b03c661e554836709) (L 0x100000000128d78869fb74632853553))) (N (L 0x10000000030b0830449ddcd65e26156) (N (L 0x1000000006a464465c9d8dee62dab16) (L 0x100000000c85296375d5386b31ba4cf)))) (N (N (L 0x10000000150694e71d5a4f95458a589) (N (L 0x100000002005692c5f8a67bbd614fee) (L 0x100000002cdfa9803937634225714ec))) (N (L 0x100000003a7433cefd6cef004317c8e) (N (L 0x100000004760130d287d89becde3d4e) (L 0x100000005239a4dc06dcfd5471a8353))))) (N (N (N (L 0x1000000059db80efd18f2aacf0637c8) (N (L 0x100000005d91b9ccb7bb8dd975ef977) (L 0x100000005d329f5e91804366fe58851))) (N (L 0x100000005914919727c2b0d9c0c240f) (N (L 0x1000000051f0899d61557081dec8b22) (L 0x1000000048b686603d3f6dbde33a15a)))) (N (N (L 0x100000003e62b2eb88dac492447d98e) (N (L 0x1000000033d9996fcd21f15c646c5e0) (L 0x1000000029d145bf18f01bcd1e882ca))) (N (L 0x1000000020c739a376dd418be1d35cd) (N (L 0x1000000019018019891a6a1d4efab90) (L 0x1000000012970d25cd598d51a7aab31)))))) (N (N (N (N (L 0x100000000d7bce0d30e96f2099bf3fe) (N (L 0x10000000098d3d57a047487cd4f60f7) (L 0x10000000069d7184d459f869dca65e2))) (N (L 0x10000000047b9632d7edc7c2ccb70b0) (N (L 0x1000000002f99a0f3803404c53d7bac) (L 0x1000000001ef5fe8fa712e404f1402e)))) (N (N (L 0x10000000013c053d2da8e322f985d7a) (N (L 0x1000000000c5dcc6b2af6c910efbc0d) (L 0x100000000079a91d76e3350ee24f2af))) (N (L 0x10000000004981d833b6dfa8ce05211) (N (L 0x10000000002baa75f1caa59bbab9331) (L 0x10000000001984126138c27203ceb4b))))) (N (N (N (L 0x10000000000eac8aca948106f1a8c8a) (N (L 0x1000000000084f20a841f746283d357) (L 0x100000000004a277552ef4125c7a245))) (N (L 0x1000000000028c28336511d977cd9d8) (N (L 0x10000000000161639de2e52edc0cb26) (L 0x100000000000bcd9cf7f7c2fb6469b6)))) (N (N (L 0x10000000000063905a818388e2b3fa7) (N (L 0x10000000000033cd549a7ca96248856) (L 0x1000000000001a9b5901931e1e6bd91))) (N (L 0x1000000000000d7eb586ef9c07d413a) (N (L 0x10000000000006c2ce36637598f0b3a) (L 0x1000000000000358c4d7f9ecf6f3da2))))))) (N (N (N (N (N (L 0x10000000000001a3273c40326f47569) (N (L 0x10000000000000cab70a72979d8097c) (L 0x1000000000000060f0f2e32f0f9fec5))) (N (L 0x100000000000002dd9aa0724c5f07af) (N (L 0x100000000000001573e78c547dcaaed) (L 0x1000000000000009ee87155be7aa8b5)))) (N (N (L 0x10000000000000048cedf2b12ae1909) (N (L 0x1000000000000002105657818e43188) (L 0x1000000000000000ed3cdb5d21c77ab))) (N (L 0x1000000000000000697c9216ca7229a) (N (L 0x10000000000000002e7464735ff45a2) (L 0x10000000000000001443ee43451e54f))))) (N (N (N (L 0x100000000000000008c24018820a0ab) (N (L 0x100000000000000003c04dc08b35dbc) (L 0x1000000000000000019799c7b34d351))) (N (L 0x100000000000000000ab7c5b117c195) (N (L 0x10000000000000000047861c11d029c) (L 0x1000000000000000001d93e4d88fbfc)))) (N (N (L 0x1000000000000000000c210b4990e5a) (N (L 0x10000000000000000004eecf419f4e4) (L 0x10000000000000000001fd69ccc52f4))) (N (L 0x10000000000000000000cbda8fabdff) (N (L 0x1000000000000000000050ef50722d4) (L 0x100000000000000000001fe2453cca6)))))) (N (N (N (N (L 0x100000000000000000000c76e93aad8) (N (L 0x1000000000000000000004d609fe910) (L 0x1000000000000000000001dcc73792c))) (N (L 0x1000000000000000000000b644225cb) (N (L 0x1000000000000000000000452cb8667) (L 0x10000000000000000000001a1106435)))) (N (N (L 0x100000000000000000000009c0dc3e7) (N (L 0x1000000000000000000000039fc6384) (L 0x1000000000000000000000015660e5c))) (N (L 0x1000000000000000000000007d7ea19) (N (L 0x1000000000000000000000002db10a9) (L 0x1000000000000000000000001086bb9))))) (N (N (N (L 0x10000000000000000000000005f0441) (N (L 0x100000000000000000000000021ec74) (L 0x10000000000000000000000000c08e8))) (N (L 0x1000000000000000000000000043e21) (N (L 0x1000000000000000000000000017c85) (L 0x100000000000000000000000000847f)))) (N (N (L 0x1000000000000000000000000002dda) (N (L 0x1000000000000000000000000000fc5) (L 0x1000000000000000000000000000564))) (N (L 0x10000000000000000000000000001d4) (N (L 0x100000000000000000000000000009e) (L 0x1000000000000000000000000000034)))))))

private def cpos_lf_242 : FastDTree := dleaf cpos_bt_242 0xffffffffff2a617d5af5ad6da8d545 0xfffffffffff8f4b84e095f5718fdf6 0xffffffffffd3b1ddaf27b0ee02cf8a 0x10000000000024dbeed609855e51c75 0xd5bc3b922e414ded8804 0x2c5d74fa051c6d0527ef (M 0xffffffffff31fd62c364cf96d1f435 0xffffffffffe2d6bd869038e2b2d16a 0xffffffffffd34adc53dad08956eeb7 0xfffffffffffe9a8c56c2dc73823921 0xffffffffff75490d093690ea5590f9 0x1000000000150d23e8218de011b28a1 0x10000000000fcfc8168522749b7e281 0x1000000000113dd83b3472ba9eac195 0x2cbab88de7428d9be40c (Z (Q 0xcd3fb6f5eab8b81ab09a 0x162fa6e3757f4260e7343 0x1764deab3e4bd2e8ef9d0) (Q 0xd2e6331d4439825280cc 0x176c997da1674240e113e 0x1764deab3e4bd2e8ef9d0))) (M 0xffffffffff46bece8d3cffcb323de2 0xffffffffffbd168728c7c4f793ad79 0xffffffffffd39f0896b02a45b69891 0xfffffffffff743dcf9b780f312f2b8 0xffffffffff42b200407d058ea500e6 0x100000000010b1b06a766bd812cf1ba 0x100000000009b48f22a06bd4d86b0a1 0x10000000001161f2c1a515f2b4a54ca 0x2d3af11982e32aa02107 (Q 0xc4f7e1d02725cfa192a5 0x14762d6d7c5a369af89cc 0x13e8932498bb0aa520ff5)) (M 0xffffffffff6067fc828c79b3c69c4b 0xffffffffff9ffb96c4f20d4327a1cb 0xffffffffffd55aeb23efc7f30e9e3e 0xfffffffffff048ddfeddcd6a53906f 0xffffffffff25f5629b5bfe17e0c859 0x10000000000c73a66bc1c47fd87a622 0x100000000004dc86fc065f336452229 0x1000000000106a41fff7480fc38136e 0x2d72c9c3824b46882b57 (Q 0xba404baa665af91e9b38 0x1275a99ba53fdb54048e7 0x111eac32acc4f70d0b687)) (M 0xffffffffff7c8b4f508f274381d5f0 0xffffffffff8b0eeae842649259873c 0xffffffffffd84f563503b217a65680 0xffffffffffe9ef55e7bea6391f3b35 0xffffffffff1a51a1c2565229541190 0x1000000000088a551c204f6146b0334 0x100000000001219471afaa96e525f05 0x10000000000ecc19cccc9e5d0be4d57 0x2d6940e424cff9ab7ba9 (Q 0xaff1743c5d013b19951a 0x10b416712a14b796d8994 0xed72733aba1f1ffddd0e))

private def cpos_bt_244 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0x100000000067ac2cbb994184ad97def) (L 0x100000000197dffe58c9cd77ae0462e))) (N (L 0x1000000004a7f6e168285ce8cd6cd81) (N (L 0x100000000b208ff7a8d590f661cfae4) (L 0x1000000016cd01f95389f041565d39b)))) (N (N (L 0x1000000029505bffb791191c9019163) (N (L 0x10000000438eb556ed7dd8dd39030cc) (L 0x1000000065321ccb602399c08fb7f21))) (N (L 0x100000008c69c53a61dd694c3ba27ba) (N (L 0x10000000b60eb03d8fd695bb32ad120) (L 0x10000000de1fc80b9356211930dc4e5))))) (N (N (N (L 0x10000001007b410d3cb8693fc2c8c0d) (N (L 0x10000001199d7f2be9cbbda09a0255e) (L 0x1000000127381d77ff1bec1be0ebcf2))) (N (L 0x10000001287ea2db7b44c84e9228910) (N (L 0x100000011e21ecfe438d74479da189c) (L 0x100000010a06e478f117d3306c1d4cb)))) (N (N (L 0x10000000eed43e8848baaf69dea6f9e) (N (L 0x10000000cf75cf2a6b1eb26faddf73a) (L 0x10000000aeaf73f1c1185d629e196ac))) (N (L 0x100000008ecf80726f450b071ae3738) (N (L 0x100000007185fbd4d564957b6fb3169) (L 0x1000000057dd33c73fb1a1b1b74ad55)))))) (N (N (N (N (L 0x10000000424af8f963131115aa53cf1) (N (L 0x1000000030d01cf680f443381e0d50f) (L 0x10000000231cc27f0d33b7a8bc2b24a))) (N (L 0x1000000018b284be4c3f80c0cb46a0e) (N (L 0x10000000110059c1248ce3a10c2ccc1) (L 0x100000000b769dc92516c6f091166a8)))) (N (N (L 0x100000000793896c7711980712cb910) (N (L 0x1000000004e961cdf2e0042f170db70) (L 0x10000000032018a82625e5131eacb82))) (N (L 0x1000000001f4055b17072a9a9d8e713) (N (L 0x10000000013314daeb6b18b228d91da) (L 0x1000000000b96d3a0d6db59e20b03c2))))) (N (N (N (L 0x10000000006e250faee1db2ab12207e) (N (L 0x1000000000406482a48e9c83cf42a69) (L 0x1000000000251117a63d396788b4152))) (N (L 0x10000000001504a75e89f67d8aaf33c) (N (L 0x10000000000bbea62d47af87b188c9a) (L 0x100000000006784840f1d8059a03fed)))) (N (N (L 0x10000000000383cde6b08a247f38134) (N (L 0x100000000001e2409dbc96dbd9dff3e) (L 0x100000000000ff11833d5522eaa1dbd))) (N (L 0x100000000000852d7d76b4c0bc6b579) (N (L 0x10000000000044a9fd9cdbc9b8e93c6) (L 0x10000000000022f7e2a9cf1a16546f9))))))) (N (N (N (N (N (L 0x10000000000011984a81065652902ad) (N (L 0x10000000000008bfd9c0d5a770777c2) (L 0x100000000000044d094378ecfc36122))) (N (L 0x1000000000000217277153f47b68180) (N (L 0x10000000000001013f62a26d269fe51) (L 0x100000000000007a533b29220f63cea)))) (N (N (L 0x10000000000000398d749dcf634ccec) (N (L 0x100000000000001acc0e0ca55e6878d) (L 0x100000000000000c59a04b6e0ea0b15))) (N (L 0x1000000000000005a29156e8cfeb921) (N (L 0x10000000000000028bc156a73161c5c) (L 0x100000000000000123a15320e430ece))))) (N (N (N (L 0x10000000000000008141d024af4ec7c) (N (L 0x100000000000000038c1e09b0d94227) (L 0x100000000000000018b1db8458a21a9))) (N (L 0x10000000000000000aa5e5f640ac658) (N (L 0x1000000000000000048cfd14d61a4b5) (L 0x100000000000000001ed906b33a0509)))) (N (N (L 0x100000000000000000cf515007efd90) (N (L 0x100000000000000000565967ba3edf1) (L 0x10000000000000000023aac5dc6882d))) (N (L 0x1000000000000000000e9cc036ed203) (N (L 0x10000000000000000005f037e2f13af) (L 0x1000000000000000000264ea99c755c)))))) (N (N (N (N (L 0x10000000000000000000f52f90f1b51) (N (L 0x100000000000000000006153f21bbff) (L 0x10000000000000000000265790b96a2))) (N (L 0x100000000000000000000efdeade6b8) (N (L 0x1000000000000000000005d1943cad3) (L 0x10000000000000000000023def7f75f)))) (N (N (L 0x1000000000000000000000db8d48203) (N (L 0x1000000000000000000000536480340) (L 0x10000000000000000000001f7432d97))) (N (L 0x10000000000000000000000bc82f6f5) (N (L 0x100000000000000000000004621ced0) (L 0x1000000000000000000000019ea7e79))))) (N (N (N (L 0x10000000000000000000000098363ac) (N (L 0x1000000000000000000000003782008) (L 0x100000000000000000000000141c7dc))) (N (L 0x100000000000000000000000073d724) (N (L 0x1000000000000000000000000297057) (L 0x10000000000000000000000000ebb28)))) (N (N (L 0x1000000000000000000000000053455) (N (L 0x100000000000000000000000001d3d5) (L 0x100000000000000000000000000a349))) (N (L 0x10000000000000000000000000038a6) (N (L 0x1000000000000000000000000001389) (L 0x10000000000000000000000000006b2)))))))

private def cpos_lf_244 : FastDTree := dleaf cpos_bt_244 0xffffffffff3090bc5e695023474eff 0xffffffffffc7dfcc408618442f80c7 0xffffffffffd9f8555d1455c7b6376a 0xfffffffffff41f9a1daff875e15010 0xd6e4bdeb29c53770dc89 0x27d75ff8522bec2b08db (M 0xffffffffff3c7f2cdb1c24bc7a9a8e 0xffffffffffb1e06d6c9d926ee19e39 0xffffffffffda8db1215d675db37359 0xfffffffffff08bdfa98bdbd118a64d 0xffffffffff30697a02ef6e03aeb137 0x100000000014b41e3f7edad471c885a 0x10000000000f60bf8c5fbcc66f31430 0x100000000014db04081fdb4d441d9b6 0x28828c45dce4b87ffdf0 (Z (Q 0xd057aeeb391c163ea17a 0x17e2e9a083ce8887393f4 0x19e97b44605087ff25e0b) (Q 0xd4b9a688668bc6a86b02 0x19128997c9a5cedc369df 0x19e97b44605087ff25e0b))) (M 0xffffffffff59aef2517897aa1b5eb4 0xffffffffff8db31656b0cf687ec2ff 0xffffffffffdcd7292accf888bcbdda 0xffffffffffe9b11b12c8fb677b7674 0xffffffffff01341a3c6eb4a428bf9f 0x10000000000f7b9924eb67cc908d4dd 0x100000000008797f0ffa8ded141f406 0x100000000014a532f87b204dc085aad 0x29a3b620ce61ebafdf83 (Q 0xc9ce6dfbd97c796f35fb 0x1635f17614ca833aa35fa 0x1651258bf6ba531ab8536)) (M 0xffffffffff7b2acccebed80d9e829b 0xffffffffff73cafd017f868ef4c5e7 0xffffffffffe0770d0e48ab9a0c6ebb 0xffffffffffe381b6d19ddaa6af4ad8 0xfffffffffeeab31a90e4ccf06eb004 0x10000000000a7c5198e74e3f096948b 0x100000000003019d201852ed1fc78db 0x1000000000132bc4b54042ee722cedd 0x2a8037c9310d8fc5e309 (Q 0xc123861aa90c2a30e86f 0x1441a2b054f96020a34ac 0x1367bee17c831e7534e69)) (M 0xffffffffff9e3555ee692fc6d67b3c 0xffffffffff6370f8283fac1d616ec7 0xffffffffffe52fcc5aebedd4a6d409 0xffffffffffde3ec37002536faa99fc 0xfffffffffee76b50298bdcff80a6f1 0x100000000005f560284ebe355183ca5 0xffffffffffed671e016e6b8320294d 0x100000000010f51df55c74dc3a28796 0x2b1bc5a6a85697226f96 (Q 0xb8974c6e768d5fab1060 0x12855ce978240d596f7b0 0x10ff4d88f2619e5ea5e98))

private def cpos_bt_246 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0x10000000007a85a93acc64b412f94d4) (L 0x10000000021d1d58aa8e385d1b3f3ff))) (N (L 0x1000000006d4c90775bdb70bd950726) (N (L 0x1000000011d5657fa53134268246c55) (L 0x10000000279bd6bbef8dcd3c0074b3d)))) (N (N (L 0x100000004d4d4987bbc32e5d1d9daa3) (N (L 0x10000000877d6030dc9cc66a6ce057a) (L 0x10000000d8a7edcefe70bf74bb3eee9))) (N (L 0x100000013fd4bfd416f2fc1394c2137) (N (L 0x10000001b7e7bd06858189ee13a97f8) (L 0x1000000237eb54a0ec4542f22557641))))) (N (N (N (L 0x10000002b456b1cad3e3f3ac450f33b) (N (L 0x1000000320fef9e72282d0b98690301) (L 0x100000037332d814fed6d33994dd519))) (N (L 0x10000003a37a6fca58a1310a11a3e55) (N (L 0x10000003ae9b493016f3986832411de) (L 0x1000000395bb50847dfcc0cacb7c9a2)))) (N (N (L 0x100000035dba7793f817ec6ebb5f2cd) (N (L 0x100000030e052d4e79691b0f64c3c7a) (L 0x10000002af32ed335c82c14eb9d1c83))) (N (L 0x1000000249bcef6f79092eb0ebfd681) (N (L 0x10000001e501d2d4d992a11dc958e25) (L 0x1000000186ae2c53ab41cf46c15e139)))))) (N (N (N (N (L 0x10000001328801a4e5690bda8b4b182) (N (L 0x10000000ea897e1633d1925ac4554af) (L 0x10000000af2f10ea23a4441e592513b))) (N (L 0x100000007fdd2d2e520f1cea7b94004) (N (L 0x100000005b4738d85c23c51e4340dec) (L 0x100000003fc8d56eb848b60bf5b251d)))) (N (N (L 0x100000002baa2c5eb6222eb1623c9c8) (N (L 0x100000001d4dddaa3d18591c6910e23) (L 0x10000000134b10b5d9b0e079d93e677))) (N (L 0x100000000c78122277c57e1dc61210c) (N (L 0x1000000007ea5504d4f913484fac44a) (L 0x1000000004f0288b998f6beb930d4ff))))) (N (N (N (L 0x1000000003077c147047109daf2aa78) (N (L 0x1000000001d3fea105d9c99c7d8fc41) (L 0x100000000115f9e3be64d1a6c67b213))) (N (L 0x1000000000a29449b845130fe55f55d) (N (L 0x10000000005dab3f19c75f59115c1ce) (L 0x1000000000352ecd0b6d76c6ceeabcc)))) (N (N (L 0x10000000001dc4b9058e5a68917e956) (N (L 0x1000000000106ebdea02e52d6dd94c8) (L 0x100000000008f2e9cf57dbed50e78eb))) (N (L 0x100000000004cf31329b4a10d927ee5) (N (L 0x1000000000028d2dd6acdc9a9bf8201) (L 0x100000000001562e7c61e322b885755))))))) (N (N (N (N (N (L 0x100000000000b10f882098585299af5) (N (L 0x1000000000005a853920bb1e6b21b5f) (L 0x1000000000002dbbfefddf5f968f7f0))) (N (L 0x10000000000016d758048b4eb529a6c) (N (L 0x1000000000000b4779f4a5b370b018e) (L 0x100000000000058223631a9b980e5d1)))) (N (N (L 0x10000000000002a93706ef4b5325240) (N (L 0x10000000000001459860dc556ebc405) (L 0x100000000000009a0104fd3ad9f3c4d))) (N (L 0x1000000000000048196eeeaafd0833d) (N (L 0x10000000000000216a93761d4817dbe) (L 0x100000000000000f55d7a1225a21673))))) (N (N (N (L 0x1000000000000006f83b0d2fa045774) (N (L 0x10000000000000032334b8efe90993b) (L 0x1000000000000001663491c8204d68a))) (N (L 0x10000000000000009e48912b70269a7) (N (L 0x1000000000000000454fb2e13cf5772) (L 0x10000000000000001e14eb99e7c9b02)))) (N (N (L 0x10000000000000000cf117ac6745d76) (N (L 0x100000000000000005851d854aecd77) (L 0x10000000000000000255a1b12c061ec))) (N (L 0x100000000000000000faa507c3850bc) (N (L 0x1000000000000000006841ef43ff53d) (L 0x1000000000000000002b0435fca81b7)))))) (N (N (N (N (L 0x100000000000000000119b74e014a70) (N (L 0x10000000000000000007267f7209b30) (L 0x10000000000000000002e1a07a16b6a))) (N (L 0x1000000000000000000126f9059d071) (N (L 0x1000000000000000000075124e419d4) (L 0x100000000000000000002e1ebcbfa1a)))) (N (N (L 0x1000000000000000000012093c652a1) (N (L 0x100000000000000000000700a126339) (L 0x1000000000000000000002b307bec56))) (N (L 0x1000000000000000000001088298251) (N (L 0x1000000000000000000000648bd7e7e) (L 0x100000000000000000000025f5520ac))))) (N (N (N (L 0x10000000000000000000000e3bb18a6) (N (L 0x1000000000000000000000054d26ff8) (L 0x100000000000000000000001f6291f9))) (N (L 0x100000000000000000000000b898396) (N (L 0x100000000000000000000000436ba57) (L 0x1000000000000000000000001877c0d)))) (N (N (L 0x10000000000000000000000008d2ea2) (N (L 0x1000000000000000000000000329944) (L 0x10000000000000000000000001205db))) (N (L 0x1000000000000000000000000066171) (N (L 0x1000000000000000000000000023ed1) (L 0x100000000000000000000000000c914)))))))

private def cpos_lf_246 : FastDTree := dleaf cpos_bt_246 0xffffffffff43e3e3962bb3c2af95cd 0xffffffffffa0c16f28881592df86a2 0xffffffffffe3d73e83b0a20c7a6702 0xffffffffffec2005de9075bae2e9d1 0xd2d9092cffaec9abffb7 0x2277795daae7c24e5424 (M 0xffffffffff53cef705a4ef68563843 0xffffffffff8bef5b74ebb7f3f6762d 0xffffffffffe536ce5481be74594754 0xffffffffffe8f8ec87ffee171cf791 0xfffffffffef1a14eace4f8bac1827d 0x1000000000134e096ba5962fb3ab6ee 0x10000000000e394d1e0d2b4e3db1b2d 0x100000000018582342e48bbc24a3f62 0x2352d878bf871848ea08 (Z (Q 0xce079bb2c17087e1240d 0x1926ef239858b82e3b5a7 0x1c31efe92e9f2ae3d4677) (Q 0xd144ed0facef2655649a 0x1a44b61e891e0ade59a04 0x1c31efe92e9f2ae3d4677))) (M 0xffffffffff787c8d391d5b5ce5e42a 0xffffffffff6b6402993d3461adbd7b 0xffffffffffe90090d844d003339776 0xffffffffffe32e1c01a8c52a38af06 0xfffffffffec8a21651096f4dbabb67 0x10000000000d44eb4a5d8d2b61cf016 0x1000000000068de9c4fb1c32b41ea35 0x100000000017a512240ea1a49924887 0x24df062f44307a5f3a8c (Q 0xc91e53c6f0db1e3ba40b 0x178dc43c9f490b1824435 0x18895389fc175e9e98b4d)) (M 0xffffffffffa08297aa0b03107d5051 0xffffffffff569c4e57edfffff32e2e 0xffffffffffedfa0f4097d484f7b3b3 0xffffffffffde530a74689d8c1a5a1e 0xfffffffffebb02879633c95dc0b00a 0x100000000007995f10108b121b98fe3 0x10000000000085743a86b7567191eec 0x10000000001589839edf92482703a59 0x263201a29cdf1f57f426 (Q 0xc27364ca2556e7031a58 0x15afd4b57f0b79023e908 0x158b210bfaf0b7193918f)) (M 0xffffffffffc8db7d9af088c832bcb6 0xffffffffff4c90ccf3010ade8220fe 0xfffffffffff3d8e70240fb419dafcb 0xffffffffffdaa0b75d866d7a4c63f8 0xfffffffffec272878a09f0d27d00fd 0x10000000000291560a5038ef943d71e 0xffffffffffbff9105cfd144ba8b81a 0x1000000000129e7d983ddab4b6adbf8 0x274c693ca3da0b227255 (Q 0xbbb75e7d3249646bbe94 0x14032fe5128b63f6ea9c4 0x130b55eb1977e2d01526e))

private def cpos_bt_248 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0x10000000008d5f25b9ff87e3785abba) (L 0x1000000002b88f975f48b5137003ecc))) (N (L 0x1000000009aba7fd80a5b5ce29ed6a1) (N (L 0x100000001b7bd1afca0842e2e942540) (L 0x1000000041f97ff3804b832abb646d8)))) (N (N (L 0x100000008a6191f3ee2d781f5777ee4) (N (L 0x10000001037ee47bb83c10b70ee6282) (L 0x10000001ba48708c0a34545d6ff1d91))) (N (L 0x10000002b5b4b9e7a5e19794c78c1c9) (N (L 0x10000003f2fe966593288310a48b623) (L 0x1000000563a832b94e6acde33f2e6ec))))) (N (N (N (L 0x10000006ee1a29b24e52b6d6d859df7) (N (L 0x1000000870f42f934c8e0296ae665ea) (L 0x10000009c852b5687cd147bc7cbdbdf))) (N (L 0x1000000ad3bd88fe16ba01d68003951) (N (L 0x1000000b7b54164cc672668ba648d76) (L 0x1000000bb31ab742180167012c444be)))) (N (N (L 0x1000000b7be1f5232b5cdd6f532f4b5) (N (L 0x1000000ae1e455388edd5d29dcbf925) (L 0x10000009f9b76f4aee8a8900c7931a5))) (N (L 0x10000008dc6d6a659276c139c02605c) (N (L 0x10000007a3c1dafc0547885087866b9) (L 0x1000000666f9312021e6503f9f92b39)))))) (N (N (N (N (L 0x1000000538ce4cd45724aec0367f252) (N (L 0x10000004267f223f1db373f689c7200) (L 0x1000000337d097e64edffeb67927dbe))) (N (L 0x100000026fc220703f2e0d81198a849) (N (L 0x10000001cda1c395856089b3a42ee1d) (L 0x100000014e3af615fceeba6e181c3c9)))) (N (N (L 0x10000000ecedb3918b5a90bbdd39bf9) (N (L 0x10000000a4909775812af3be50dd453) (L 0x100000007013412b20e3acc37f73c96))) (N (L 0x100000004ae3ae6cb9afe294a821b0c) (N (L 0x100000003120f90f9e688b4c32238bf) (L 0x100000001fa8e9097029d020f56f665))))) (N (N (N (L 0x10000000140d7ccc63e175b82211273) (N (L 0x100000000c7d5c0355f268a161edc75) (L 0x1000000007a745fecc4266f1d09af1a))) (N (L 0x10000000049dbd5688a1910f2f03a31) (N (L 0x1000000002bddff2f5b0c791c11d933) (L 0x10000000019aaa08fd2253d7505a30c)))) (N (N (L 0x1000000000eccb8690b9aa237767857) (N (L 0x1000000000869c2fd97cb67533a5f89) (L 0x10000000004b7777f192e7191afff3f))) (N (L 0x100000000029bd67f9f484a70ef7c14) (N (L 0x100000000016c85c3c1e7b16e9a1180) (L 0x10000000000c46977d16facdec05c07))))))) (N (N (N (N (N (L 0x100000000006880c71047618b583556) (N (L 0x1000000000036eb75a00f7366003980) (L 0x100000000001c8402f420a6b77e8ff1))) (N (L 0x100000000000ea1ce1cabc870bc2d51) (N (L 0x10000000000076bf1596bace8e245d2) (L 0x1000000000003b8d2b9097bb1cc26b1)))) (N (N (L 0x1000000000001d88ffcb0a639a7da72) (N (L 0x1000000000000e7d55fce6a75c6f374) (L 0x10000000000007086c4128a0dd9c605))) (N (L 0x1000000000000360c5f02e54a834938) (N (L 0x100000000000019b1d9b43b3612731b) (L 0x10000000000000c17b82c382a42ceaf))))) (N (N (N (L 0x100000000000005a28f541420d13c85) (N (L 0x10000000000000299b28b017e6a8959) (L 0x100000000000001304608925fcd761d))) (N (L 0x10000000000000089c61e6919d7f0c4) (N (L 0x1000000000000003dcf2e194f8daf83) (L 0x1000000000000001b7a77c04033fb75)))) (N (N (L 0x1000000000000000c1b718c2d4231f0) (N (L 0x1000000000000000549ac25ca5c8e03) (L 0x100000000000000024a1ce52f5f9d76))) (N (L 0x10000000000000000fb9ebebe9b3622) (N (L 0x100000000000000006b1e37fdfb8803) (L 0x100000000000000002d39dbf941ca8d)))))) (N (N (N (N (L 0x1000000000000000012f0982ce3c55b) (N (L 0x1000000000000000007de44bd5b2715) (L 0x10000000000000000033e337b386f21))) (N (L 0x100000000000000000153849aa16e77) (N (L 0x100000000000000000089c9174f5811) (L 0x1000000000000000000377ea94c5402)))) (N (N (L 0x1000000000000000000162f4850d884) (N (L 0x100000000000000000008cdad8b6482) (L 0x10000000000000000000377d493c146))) (N (L 0x1000000000000000000015b4184727c) (N (L 0x10000000000000000000086dcd308b7) (L 0x1000000000000000000003402d0af80))))) (N (N (N (L 0x10000000000000000000013eba31d8f) (N (L 0x1000000000000000000000793e8f608) (L 0x10000000000000000000002dcfdc7b6))) (N (L 0x10000000000000000000001131f7e73) (N (L 0x100000000000000000000006696ca95) (L 0x100000000000000000000002601997d)))) (N (N (L 0x100000000000000000000000dfd7af7) (N (L 0x10000000000000000000000051e03e6) (L 0x1000000000000000000000001dc2d40))) (N (L 0x1000000000000000000000000ac0425) (N (L 0x10000000000000000000000003dc2aa) (L 0x1000000000000000000000000160a5b)))))))

private def cpos_lf_248 : FastDTree := dleaf cpos_bt_248 0xffffffffff5d37a5f33511516ac853 0xffffffffff855a17dbc29373ed4cf7 0xffffffffffed58c71fbc4fd6f5defb 0xffffffffffe99db429a4fba5084bd9 0xcbd0c02b8d4fcac1dca4 0x1d2328dd269515ab6549 (M 0xffffffffff708425aa0ff8c39d8cca 0xffffffffff727c2530ac289ba4d992 0xffffffffffef3eb7dd80ebf022c88a 0xffffffffffe70b296446c70330de5d 0xfffffffffebd2c5dba85544163d576 0x10000000001125a3f51ae4a65215b38 0x10000000000c73d8862aeacb991a1fc 0x10000000001b874b2f07686243019b5 0x1e0f24697cb7c3830e39 (Q 0xc9878949e0af841dfbc1 0x1a7a888ffe11ed9b8b1af 0x1e36c5d6b05681d316ca0)) (M 0xffffffffff9b3ec96486495d9d459b 0xffffffffff570132527d6856774d62 0xfffffffffff3f52c7c91620dbffdef 0xffffffffffe2954476a0ed4ea9a812 0xfffffffffe9cbea7e934887697d859 0x10000000000a637b57078d0a55324a8 0x10000000000413e325cac86daa77ccb 0x10000000001a370923da08b3669af5a 0x1fc94eafc0c4e81718f9 (Q 0xc4c03ed4db0e1bbd95c9 0x18837b01ac5c556e58994 0x1a87bcde0b75460b7fde8)) (M 0xffffffffffc817504b34504baa45c6 0xffffffffff4891854dda1c9c7c369e 0xfffffffffff9a65fb37daecb7d8450 0xffffffffffdf4294939f321bf46b52 0xfffffffffe9a0fafb1b1aa674b402a 0x1000000000042ab32a219d3e4065452 0xffffffffffd912ec18bd8729f1d2c1 0x1000000000175dbfa769b52527f58e1 0x21599d83c1dbbc6e0870 (Q 0xbfc342c39b8386ece4a5 0x16c1835b278c2b4bbf90e 0x177e15c6c590285e6f0b9)) (M 0xfffffffffff3cb0a624aff2e53565c 0xffffffffff45c7a5af68c7cfc00a81 0xfffffffffffffd8893a2505dd2f5d4 0xffffffffffdd4176ac71915911b1c6 0xfffffffffeade216e18e09ae55edd0 0xffffffffffec6d03d3bc173508070e 0xffffffffff8cc3fd7225242566f2a5 0x100000000013a87fc0ed24693f00a0d 0x22be89a9fc8b44193493 (Q 0xba9eaa714830014ae274 0x152aed66a5f2f6e3a3a87 0x14ef9d387dd65436df782))

private def cpos_sub_28 : FastDTree := (dsplit (dsplit cpos_lf_242 cpos_lf_244) (dsplit cpos_lf_246 cpos_lf_248))

private def cpos_node_29 : FastDTree := dsplit cpos_sub_27 cpos_sub_28

private def cpos_bt_252 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0x1000000000a038a23932ab12ddbc2a0) (L 0x10000000036a36ba76f9439aac52692))) (N (L 0x100000000d46bd1e9c2823be6760431) (N (L 0x1000000028eb937c79167fcb1745178) (L 0x1000000069d9d9ab2ed04af011f17a7)))) (N (N (L 0x10000000ee0ae4a0580b14f1f8bedda) (N (L 0x10000001dca005d83858f82106c250e) (L 0x1000000360672a94bb681c902f06e79))) (N (L 0x100000059e669cd9726b8fb71d0fced) (N (L 0x10000008aa5a33138210f8ac933c26b) (L 0x1000000c7c58825ac4ed907c98435b7))))) (N (N (N (L 0x10000010eb118eb883e6717db4cd0bd) (N (L 0x10000015ad0d6af42ec9888e54c80b0) (L 0x1000001a6158f99dd7c6d13104b03fd))) (N (L 0x1000001e9de361352131be8700cc865) (N (L 0x10000022003619a85c2e94f49963178) (L 0x100000243cac85e9298fbe0423eaf6b)))) (N (N (L 0x1000002528f070516728591d696d062) (N (L 0x10000024bff26046ecb6e8c60e5cf6e) (L 0x100000231f4cce70745780314c31921))) (N (L 0x100000207f77f50e5f138abef4f3be0) (N (L 0x1000001d291079c7af9159ddb090d48) (L 0x10000019699caf58f391c059ccb5762)))))) (N (N (N (N (L 0x1000001589d199eb509a534a7d98094) (N (L 0x10000011c698eab1835ac64a6049623) (L 0x1000000e4d477efda22732d95341887))) (N (L 0x1000000b3ac52309251fac10c765773) (N (L 0x100000089cf683840fb13922200a7d6) (L 0x10000006758da852435e10cbfb31049)))) (N (N (L 0x10000004bd6f788853df27be2c2d746) (N (L 0x1000000368092f23df2c207e8b09df9) (L 0x10000002662aadef087d54119ec9218))) (N (L 0x10000001a832489b147cf9014479c28) (N (L 0x100000011f827bc685ee705de9439ef) (L 0x10000000bf569a06f2427a7b969f204))))) (N (N (N (L 0x100000007d19b642562c80f869b96aa) (N (L 0x10000000506640a0a17f3d33fab61a2) (L 0x1000000032d0e8846d8693f9e0254b7))) (N (L 0x100000001f99fae7320aa824998cc0f) (N (L 0x1000000013584bb9bfe8aacb9e5581b) (L 0x100000000ba9657a1bc25460c7d653d)))) (N (N (L 0x1000000006ecff6a35cf4b644c1604b) (N (L 0x10000000040dbedd31f3f55521cf8d3) (L 0x100000000256d6036601c55ae56a947))) (N (L 0x100000000154ceca40a608e5236039f) (N (L 0x1000000000bf5aca44887c29e981f84) (L 0x10000000006a07f6e969cbbc4c74dd5))))))) (N (N (N (N (N (L 0x100000000039ffd5ad0efcce093db6a) (N (L 0x10000000001f53fc753dd7bd07cfaf6) (L 0x100000000010b6d343d6862dd203b29))) (N (L 0x100000000008cf6fe281b28180f50f4) (N (L 0x10000000000496e74cc000f1554236f) (L 0x1000000000025cfc337856d341d2dcf)))) (N (N (L 0x1000000000013401a67ba07846dbe00) (N (L 0x1000000000009b1380288169c33440f) (L 0x1000000000004d3b438240539ef8485))) (N (L 0x100000000000260dc7e976ee726b8ef) (N (L 0x100000000000128de4fa8528201baea) (L 0x10000000000008f436e085b8200859d))))) (N (N (N (L 0x10000000000004470c518b52e6cb129) (N (L 0x1000000000000205f5b92566cde01da) (L 0x10000000000000f29db37fdd056b252))) (N (L 0x10000000000000708ed886a8cd4ba38) (N (L 0x1000000000000033bab8b7bf98b4d05) (L 0x10000000000000178de8175064beb3f)))) (N (N (L 0x100000000000000aa0b60b180f5aa1a) (N (L 0x1000000000000004c0a00d5c1fe5e36) (L 0x10000000000000021b41c89a26f7cf1))) (N (L 0x1000000000000000ecf394a348a89cc) (N (L 0x1000000000000000673ae4d6f08333c) (L 0x10000000000000002c987c9ab8b0e1b)))))) (N (N (N (N (L 0x1000000000000000131b2d61a07ce30) (N (L 0x1000000000000000081e76778c83dc6) (L 0x1000000000000000036c2275c28255f))) (N (L 0x1000000000000000016e651ea143cb0) (N (L 0x100000000000000000980780c6798d8) (L 0x1000000000000000003e98c4ec64bb4)))) (N (N (L 0x10000000000000000019940295906c3) (N (L 0x1000000000000000000a5f9d5c6f0c1) (L 0x100000000000000000042d0fdbd45b5))) (N (L 0x10000000000000000001ab3bd6942e7) (N (L 0x10000000000000000000a9828117168) (L 0x1000000000000000000042c7144ebe2))))) (N (N (N (L 0x100000000000000000001a1f5a8232d) (N (L 0x100000000000000000000a25e70a613) (L 0x1000000000000000000003ea56b4305))) (N (L 0x1000000000000000000001801e8250b) (N (L 0x10000000000000000000009238e0294) (L 0x1000000000000000000000374bb2116)))) (N (N (L 0x100000000000000000000014c6513db) (N (L 0x100000000000000000000007c1409ce) (L 0x100000000000000000000002e05b59e))) (N (L 0x1000000000000000000000010f68a91) (N (L 0x100000000000000000000000636a5b0) (L 0x1000000000000000000000002431112)))))))

private def cpos_lf_252 : FastDTree := dleaf cpos_bt_252 0xffffffffff7763e581a528b61d1aef 0xffffffffff73e45f0ea7316bbe53ed 0xfffffffffff498bd25816b89683d2e 0xffffffffffea485f8edd2f9aae7cab 0xc3af4187c7ae77959db2 0x188774684e40b377a020 (M 0xffffffffff8d5c6094652f24476bfc 0xffffffffff6371e0b6836cee699e1c 0xfffffffffff6c4d1c52593295e1ba9 0xffffffffffe8508f247c8359f8634c 0xfffffffffe948a9b0b5d8d36caf82b 0x10000000000e8c58276ab83e905bd52 0x10000000000a351f80549af4a29b707 0x10000000001e4abc9928338ef19ca59 0x196baf28df5ef94c7881 (Q 0xc20a5442ebb9aad29e0b 0x1af9b6d39ea4561f457d2 0x1ff72cd3c645c23dcd968)) (M 0xffffffffffbc8d00ef5e556e441928 0xffffffffff4dcbdf50a488580d84df 0xfffffffffffbe107869290468c4a99 0xffffffffffe52f3f474f1ff3bd7101 0xfffffffffe7e6acbdc744ae8379c42 0x1000000000072f83e7635c1374d8976 0x10000000000136073a81dbb4acc3048 0x10000000001c42892fb9b125f9bebf0 0x1b21582ea8f752516991 (Q 0xbe8a88966ef0d3ebdb24 0x1925bb5935347f9728bb6 0x1c492d056affc7cd051f9)) (M 0xffffffffffec6f474ab2cabce3ea4e 0xffffffffff4635c44a88c02864e70a 0x1000000000001bc77ce00f609052a22 0xffffffffffe35208b80d4b89d5c1f4 0xfffffffffe8806e1231613f9ccc12e 0x1000000000008de710fd341b61362a0 0xffffffffffa545b69f3a95e092ffdc 0x100000000018964034701ae42119687 0x1cbb6884b0255f8dd189 (Q 0xbad13d0559270715c6df 0x17813e59521be7493c747 0x193b7a789590596a27f4b)) (M 0x100000000001990fe663f3928d43349 0xffffffffff4ae17b2857f9846f5b50 0x1000000000007fad31a38afb9f918f2 0xffffffffffe2db0ba3cadc38c5aa75 0xfffffffffea9200ecf76c3e6480906 0xffffffffffaf7117f8084305fedbd6 0xffffffffff56fd91844ab316599fc9 0x1000000000140833a3baa4c99dbc707 0x1e379118f1461c04b525 (Q 0xb6ea2e0d1b450cac456e 0x16036125f9d2bc0c98f11 0x16a57d7890e963bc9dd03))

private def cpos_bt_254 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0x1000000000b3121eb865ce42431d986) (L 0x10000000043212c1f19fe3f2d02ab50))) (N (L 0x1000000011c031c5db8ccb6b39c5817) (N (L 0x100000003b1b3bfcfd7ba4b9e85231b) (L 0x10000000a441130a286ebbe6f0a01b2)))) (N (N (L 0x100000018b0bdb947fb738b13f8dd3d) (N (L 0x100000034acd636468c829edb685bd2) (L 0x10000006577fdf2dbd3356ba45a2744))) (N (L 0x1000000b2db34c09de790017a2f44b1) (N (L 0x1000001237f15c5a0bfd58d1861ef89) (L 0x1000001baeb56ffe2cf445bec8c35ca))))) (N (N (N (L 0x100000277b72fb3c1fc01c75992a538) (N (L 0x1000003527dc26f5a414507ca757c41) (L 0x10000043e0157a49083e09690158ba4))) (N (L 0x100000528980cdf3a23146271570a5e) (N (L 0x1000005fea08b769a9a328eb42af3af) (L 0x1000006ad7516c71209bca9132466a1)))) (N (N (L 0x100000726357d1b29f80379dad19681) (N (L 0x10000075fd334c7ddc31227661ca120) (L 0x1000007580382ef705dc2bd1008172c))) (N (L 0x10000071304d25b281e11c72d15faf9) (N (L 0x10000069a67a9048dcee8ae2e061f41) (L 0x1000005fb383cf86a268f24e965fae1)))))) (N (N (N (N (L 0x100000543f4acf00d4dc18b1d99dcae) (N (L 0x100000482b01497e7b999dfc8733748) (L 0x1000003c3a537c456fd0d40e7b40212))) (N (L 0x100000310579245692c86b2edafac45) (N (L 0x10000026f40f63dfdea12f54174fe67) (L 0x1000001e3f2a56a115beb550c90909e)))) (N (N (L 0x10000016f850b5d2b0566c96403e50a) (N (L 0x1000001112fc1c7b3e019720f9f8c2a) (L 0x1000000c6e9488385580149837af0a1))) (N (L 0x10000008df74d145e07a8e867fdaef9) (N (L 0x1000000636270fe0fba73610ef794d5) (L 0x100000044492177d9446d26268efa2d))))) (N (N (N (L 0x10000002e13433e245ea745606175d4) (N (L 0x10000001e8c0cdad3eb0e395b1795c6) (L 0x100000013e8cf4b7cc5ffba6f7928fe))) (N (L 0x10000000cc3454e6367740e7d37c474) (N (L 0x1000000080cf5547d199c040bfdf949) (L 0x100000004ffcb155c542f8e13021e0f)))) (N (N (L 0x1000000030eaa82068072cd103ae7c5) (N (L 0x100000001d792ec38521b95a68aa470) (L 0x100000001180a8d89a6b4b3d29acfed))) (N (L 0x100000000a3f6b34434f73274f2e697) (N (L 0x1000000005eaef8578fb29b08e54e0f) (L 0x10000000035f1a37457cf5b5ec9355a))))))) (N (N (N (N (N (L 0x1000000001e54bb7b6c3b2e28fefcf3) (N (L 0x10000000010d5fafb54cb55a019e7c2) (L 0x100000000093a642a3e51aecf334e9c))) (N (L 0x10000000004ff02a4d859d0d8932023) (N (L 0x10000000002ac27ea0f3ba27a209d42) (L 0x1000000000169a99b41e5944e39fb31)))) (N (N (L 0x10000000000bcfbbef9c2da53af2fa1) (N (L 0x1000000000061a324b9d228b2a26971) (L 0x1000000000031e2bd82fc49c8e049b7))) (N (L 0x100000000001936216e4c9693ec11b6) (N (L 0x100000000000c9b15302e5d2f98a2aa) (L 0x10000000000063caf77b8e87f53a5d8))))) (N (N (N (L 0x10000000000030de53bab0da0696021) (N (L 0x10000000000017b08bde792e4be68f1) (L 0x1000000000000b5ec1967e145ab694b))) (N (L 0x10000000000005677559776b8bb2de9) (N (L 0x100000000000028b41779e7e42e0f61) (L 0x100000000000012fb0f49b9d0ae88ef)))) (N (N (L 0x100000000000008c4e50c6f1cade774) (N (L 0x10000000000000403b47437a0421b5c) (L 0x100000000000001d243f179a406f599))) (N (L 0x100000000000000d1ad73edf1d79f81) (N (L 0x1000000000000005d78fdffd77b7d34) (L 0x10000000000000029502d30ec874bae)))))) (N (N (N (N (L 0x100000000000000121b1ee76ef98464) (N (L 0x10000000000000007de8a8b56d853e2) (L 0x10000000000000003646a211a37f31e))) (N (L 0x100000000000000017355ad0e2e1d20) (N (L 0x100000000000000009d85a918b44307) (L 0x10000000000000000424c6d10e2f5d1)))) (N (N (L 0x100000000000000001bb0451173f882) (N (L 0x100000000000000000b79c31c62fe52) (L 0x1000000000000000004b86ba4957a7b))) (N (L 0x1000000000000000001ed6344dd656a) (N (L 0x1000000000000000000c7f8f3e2e0c7) (L 0x10000000000000000005076f3cf8665))))) (N (N (N (L 0x1000000000000000000202581769f3f) (N (L 0x10000000000000000000cc0a45c1be4) (L 0x10000000000000000000506155cbbf8))) (N (L 0x100000000000000000001f72abe6f2c) (N (L 0x100000000000000000000c38646ac6a) (L 0x1000000000000000000004b783a818c)))) (N (N (L 0x1000000000000000000001ceffd2faa) (N (L 0x1000000000000000000000b05e30a30) (L 0x100000000000000000000042bfb1d22))) (N (L 0x10000000000000000000001919c320c) (N (L 0x1000000000000000000000096120637) (L 0x1000000000000000000000037ba1e9c)))))))

private def cpos_lf_254 : FastDTree := dleaf cpos_bt_254 0xffffffffff8ff1fddf92443172959f 0xffffffffff6999bc96a8973f2db574 0xfffffffffff99ebb53e5c799db3a64 0xffffffffffec1e2cc62e4a3692ce8c 0xbb8da818a70b5551c25d 0x14e174b04a31d9ec7e81 (M 0xffffffffffa7e7c11673ad3578b3c3 0xffffffffff5bc6f6ef4cbb91a0c5af 0xfffffffffffbe0799461acb0af5d17 0xffffffffffeab1ceab7cc944639e55 0xfffffffffe772a2021aabf548d2202 0x10000000000bc61a204cec42b252411 0x100000000007a3e7567f79c1359c06a 0x100000000020950df59a40483875eec 0x15b363f95cccc8ab305d (Q 0xba5bfe25667a6bcd2bf9 0x1b3ab317934a9c910757a 0x21774e9e8293605ca9906)) (M 0xffffffffffda1390fe9a20db7fd7f8 0xffffffffff4c2facca8809aba78287 0x1000000000000ffd9c6760a36482f05 0xffffffffffe8ba6cca1cd50fa5b2ca 0xfffffffffe6c71a810ff75608e9a79 0x100000000003ef9585a0e5acadf559e 0xffffffffffe1edf69dd6d7bc158952 0x10000000001dc040dc56e134fc88720 0x174b113d104418a49854 (Q 0xb7c4f710119e042e98b3 0x19870a0f272e2d9e42c39 0x1dcf6f5a55f1325ed2e55)) (M 0x100000000000b685663c0616a97108c 0xffffffffff4b66491d2f88be1a82f6 0x1000000000006a30166b8bb7d0b2142 0xffffffffffe81700c9ae7618b8dca9 0xfffffffffe830367f55f8af5325365 0xffffffffffd0a859c8f96f07b22bb1 0xffffffffff6fc29d5ee1d3a0f67a97 0x10000000001932a35486460114925b6 0x18d06b7c926548ff3918 (Q 0xb4f5dacdcf75011ca7c9 0x17feab83d0c718e7a433d 0x1ac30bf74b260676936af)) (M 0x10000000000385339f0477cc3c48b74 0xffffffffff572cfb3503c80b7fafb9 0x100000000000c6909f8abed806652ad 0xffffffffffe8dcc7b7f56fdc944a83 0xfffffffffeb18fd2f2bd98fcb3a599 0xffffffffff768ce86a9d5d707e6ff9 0xffffffffff218e71511b12f0964d2c 0x100000000013c4c019ea10280ac61d9 0x1a4177b947779ec636c9 (Q 0xb1f8ec7fafdb306464aa 0x16994e72ec9ef47441672 0x182af398a398ae9091b16))

private def cpos_bt_256 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0x1000000000c5eb9b3798f171a87f06b) (L 0x10000000051023adcf3c961bdb8cd02))) (N (L 0x1000000017322f4e521b77634939a87) (N (L 0x1000000053202e6b8bbb62c593ed253) (L 0x10000000f767fdacb061a5480811737)))) (N (N (L 0x100000027ac2321a844199b3b7a5ca8) (N (L 0x100000059fce00dda5fa86011002097) (L 0x1000000b7c67bbdd651d60b48d86d90))) (N (L 0x10000015693c35819922c7823e37c3a) (N (L 0x10000024d2aa072d2de9d70d8d079d0) (L 0x1000003aed609bff36bbe4fca7e5f10))))) (N (N (N (L 0x100000585c88d30cf14489066fbc6c4) (N (L 0x1000007ce0116b0c05e5bef31aa2914) (L 0x100000a723e44eb4ac2e95db62c67e7))) (N (L 0x100000d4c2a628f308dffdf218c2cff) (N (L 0x1000010281c9f85fc682079cda12d9f) (L 0x1000012cbd70b8bf140f894bcafa45f)))) (N (N (L 0x1000014fedd6c053ab497fcb89e0525) (N (L 0x1000016929e59e5468de60260a71ada) (L 0x100001768c558c7cedc99669f0df8b8))) (N (L 0x100001776959130eb38ede90364fbad) (N (L 0x1000016c4eeae71b959d041ecd81fba) (L 0x10000156d5c187b8ae1f94dc86e3050)))))) (N (N (N (N (L 0x10000139519ac3fb6dcbdc7ef74fc68) (N (L 0x100001167373bc98c3e8b2c926dd39d) (L 0x100000f0ef64e13971d4b11fbe0f5da))) (N (L 0x100000cb337fbefade30461e0e907f3) (N (L 0x100000a73707bafd6bc5d71ee583ec2) (L 0x10000086636d1471344ea9e6ac942e3)))) (N (N (L 0x1000006993d0059010bd3a32459cd90) (N (L 0x100000512514332e283b74231b012da) (L 0x1000003d0fade5909b4f7f11d27c4fb))) (N (L 0x1000002d04e80c0a3cad2e3644b73b0) (N (L 0x100000208ad6344eed2957b12cc7b5a) (L 0x1000001713e879f5b411f6943c73cd4))))) (N (N (N (L 0x1000001010bc4a8de382628036af949) (N (L 0x1000000afc0c709f94e28cef0b5eb0b) (L 0x100000076177606d93c0b88e9f115ca))) (N (L 0x10000004e03c3a90eaa02466a77881a) (N (L 0x100000032b25b7c4fd21bf12efcdb60) (L 0x1000000206bb7c6881c9349dabc5555)))) (N (N (L 0x100000014698b96ba8a6ac5576bc9af) (N (L 0x10000000ca8689425288ec6691f071c) (L 0x100000007bbdc188bd8d3e7c56676ac))) (N (L 0x100000004a852f6a4b9f73ae119c0f8) (N (L 0x100000002c3fef3b80150950daf6793) (L 0x1000000019ea7fc1dfe962fb8435513))))))) (N (N (N (N (N (L 0x100000000ef9c19e842e29551627cb5) (N (L 0x10000000088a6935f53ad187192274b) (L 0x1000000004cefec141a4c0ad343bf15))) (N (L 0x1000000002ac6a165e424af28b994ce) (N (L 0x100000000177de68b357d4159fd0eb0) (L 0x1000000000cbf2a44a653469eda95d9)))) (N (N (L 0x10000000006d5d3165ac73a49d3ce2a) (N (L 0x100000000039f864bcafc71b6e36332) (L 0x10000000001e61b0fdf4fde7f3d5a48))) (N (L 0x10000000000fbf1e4e415b26dc7a438) (N (L 0x100000000008129ff6a0c2885ebe4db) (L 0x100000000004183530747cb89f2f30d))))) (N (N (N (L 0x1000000000020e197f4db4e392acdd3) (N (L 0x100000000001055702c85c791d4c6cf) (L 0x1000000000008082cadbd792e0bcf0a))) (N (L 0x1000000000003e913c5b3980a8cc20a) (N (L 0x1000000000001e2a3ab3f29836caf5a) (L 0x1000000000000e675f8d3dfe97f8e84)))) (N (N (L 0x10000000000006d022b5a89a88ec068) (N (L 0x10000000000003315568bda77cc03dc) (L 0x100000000000017b863a8790b373ba4))) (N (L 0x10000000000000aea5f139d67fa0c27) (N (L 0x100000000000004fa8abd59fadfa1d3) (L 0x1000000000000024046244137e6014d)))))) (N (N (N (N (L 0x1000000000000010253324460f501df) (N (L 0x10000000000000072d23d9af132aa27) (L 0x100000000000000329c98b65faa07a1))) (N (L 0x100000000000000162049842854807e) (N (L 0x100000000000000099845cb9ae96081) (L 0x1000000000000000420a8a82e3c107c)))) (N (N (L 0x10000000000000001c2fdda243f0865) (N (L 0x10000000000000000beff0b5469d8cd) (L 0x100000000000000005044f7ab87a1c3))) (N (L 0x10000000000000000217af1f6b8837c) (N (L 0x100000000000000000ddc55ca2dfc94) (L 0x1000000000000000005b235ef54e22c))))) (N (N (N (L 0x100000000000000000252eb02c560b4) (N (L 0x1000000000000000000f0fa1c45c619) (L 0x100000000000000000060eb9df4eb4a))) (N (L 0x100000000000000000026b58de3056b) (N (L 0x10000000000000000000f5a85aabc5a) (L 0x1000000000000000000060c639c0851)))) (N (N (L 0x1000000000000000000025ddebbf9ce) (N (L 0x100000000000000000000eb7ef38ec0) (L 0x1000000000000000000005aef14c7a4))) (N (L 0x10000000000000000000022e2983041) (N (L 0x1000000000000000000000d4c141411) (L 0x10000000000000000000005094dcda2)))))))

private def cpos_lf_256 : FastDTree := dleaf cpos_bt_256 0xffffffffffa6240d038c31e98447ff 0xffffffffff6446ee526b9dbfe6c0c2 0xfffffffffffd25af44ff9652dde1ff 0xffffffffffee38b1f159d39c301e26 0xb3ca2310ff17c0e98506 0x12018722c5b3560d28f8 (M 0xffffffffffbf807b809f1547608162 0xffffffffff5919c596742f625044a6 0xffffffffffff5e87e60b72907b07b1 0xffffffffffed400c5669c9be88e837 0xfffffffffe63673848b2aea12035d2 0x100000000009015f584aff7d35b244f 0x100000000004e2e6fa61a3d76b7c77a 0x10000000002265df37c4d7d39fb1b9f 0x12c2aafdf69610cdc4d2 (Q 0xb2edafb4a50d3c1a42eb 0x1b50826efedd6abd0364b 0x22be468d8499f9ba6a78a)) (M 0xfffffffffff369fdc4562dc3f94e18 0xffffffffff4f6e75fc41b4046b05f0 0x100000000000445bbee1b5e0789ca3e 0xffffffffffec3915a9adfee5f54f76 0xfffffffffe64a0c5c1ab12c104c2fd 0x100000000000d17b39517d3116e9ca7 0xffffffffffaf2e5eed3d8f8d6ef8f7 0x10000000001eb5ff14bd61402869251 0x143bb5558badb9943320 (Q 0xb1043a84d65a4e88715a 0x19b948d3c671d8d3dd138 0x1f1fa0d964aee082eea74)) (M 0x1000000000024e981ef18d5a18334b8 0xffffffffff550b598a3bbcd550216b 0x100000000000979c86238a76a813b1c 0xffffffffffec8846f9afb876c47634 0xfffffffffe883f585b4cf42593e7ec 0xffffffffff9cc11af60cd4f58f1f10 0xffffffffff3ada3f75783d3aabd4e2 0x1000000000193f6c15d52eb24db1d28 0x15a6bc9111c758051c4d (Q 0xaee52ed29ce3cd75aaa8 0x184a364bd548733b16894 0x1c1810ddeefc77575700a)) (M 0x10000000000505ab852f77cc53c88f1 0xffffffffff673f1a673ebadf17787a 0x100000000000e97e1c068db005f002a 0xffffffffffee362024870e16255019 0xfffffffffec3d8614dad5e59bda4e2 0xffffffffff4438b598025105427f8c 0xfffffffffeeebb0c5e9394a00ac051 0x100000000012f19dd2ad3aa509c9d33 0x1702365de8e4d7e48b96 (Q 0xac9960acf7b1bd1c2b7b 0x16fb722c8d9b42fe4117d 0x19819d6dc10c3ee042ac2))

private def cpos_bt_258 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0x1000000000d8c517b6cc14a10de0751) (L 0x100000000604697e0fcf5a15ce78bb2))) (N (L 0x100000001db6df13131bf2353dd93f5) (N (L 0x10000000722ea02541bd623fad19e75) (L 0x100000016ae05cfd316ee78f2f61813)))) (N (N (L 0x10000003dea7c2291c756b9c9e63661) (N (L 0x100000094fea2b69145a82e0f27398c) (L 0x100000141fae9bbeefb62d97ab5b0e3))) (N (L 0x100000279afb2ef41d9237b15a9be29) (N (L 0x10000047c4ecef8e2034f66dfb115e2) (L 0x10000078cc7da9e5efca6309d41c704))))) (N (N (N (L 0x100000be35bfcf3e38e62f0fd154d31) (N (L 0x10000119dc158bea560ce79028f8f1d) (L 0x1000018b0a35316bfc7b324419ee834))) (N (L 0x1000020deb407b053eacd9eab7f5e37) (N (L 0x1000029b892313e322adee0b8a46cc6) (L 0x1000032a6b43fc2fb79fd94e34c03b4)))) (N (N (L 0x100003afbfa0a16ce70d53dc8920b38) (N (L 0x10000420d4b8f9e93b5da6faac6585a) (L 0x10000474972337cd5dbc9327d7bcd60))) (N (L 0x100004a4c7182c058e6a45e28a484f1) (N (L 0x100004aeaeb6ef2d708c3d01e68279b) (L 0x10000493419315898f95214b6857815)))))) (N (N (N (N (L 0x10000456af90a4152a4d602a940085e) (N (L 0x100003ff8f71211ab6dcce097429c99) (L 0x10000395d39450a4f1be046c59e272e))) (N (L 0x10000321bc58a8ff384d8a5f282586f) (N (L 0x100002aaf1d164e7874fb1ab2e7613d) (L 0x10000237dec575e9c8183c859ef2ccb)))) (N (N (L 0x100001cd55f728e88e745231093941b) (N (L 0x1000016e7c65ef93c403c296e09e165) (L 0x1000011ce9bc5b3b4df146f9c584167))) (N (L 0x100000d8ebe6127c67bfbd1b8f567ad) (N (L 0x100000a1db11bdabb2bb3e68cd97eec) (L 0x100000766eb1cf3dcb39eec6b60a50f))))) (N (N (N (L 0x1000005508cd6781e743b3bdac6d4d1) (N (L 0x1000003bf1cc87fe0fd43ceafd44a8d) (L 0x1000002982ff77f3da909ac0b88620c))) (N (L 0x1000001c4106aaf4fb87ac0531cf293) (N (L 0x10000012e8ebfe58b65ad637353128b) (L 0x1000000c736181dfb538492abf8d53b)))) (N (N (L 0x100000081181e3c9a46801fce380fe4) (N (L 0x1000000525e92d393b3ffa75b2411f1) (L 0x100000033c4a590547a0811d3b6d76a))) (N (L 0x1000000200f479c62442f243566f6bf) (N (L 0x10000001392270dbdc886af71cc0a84) (L 0x10000000bc7d28ee20a6daa331fbe16))))))) (N (N (N (N (N (L 0x100000006fea07ee4eec056a5864d82) (N (L 0x10000000419055ef5ded7ba86ae1875) (L 0x1000000025e8edcbd11a579997f480e))) (N (L 0x1000000015a40cc7b7ef4c39d24a02a) (N (L 0x100000000c331ba0ac2a15307e1f0f5) (L 0x1000000006cb1b75939891aa8af1d36)))) (N (N (L 0x1000000003bcd8303dab65a923f1a7f) (N (L 0x10000000020847b739d80fa88ea730f) (L 0x100000000117a67a9ab2b20e40015e8))) (N (L 0x1000000000949e5891b2fdfba86923a) (N (L 0x10000000004e1c0bf2e26440406977b) (L 0x1000000000289b5ac586bfe62dc918e))))) (N (N (N (L 0x100000000014e2b2d517345c2794fec) (N (L 0x10000000000aa13e839ec06b23150b0) (L 0x1000000000055ac64c69cf1e83aafe1))) (N (L 0x100000000002ab8897630bf17306068) (N (L 0x100000000001517642893bdaa1ef2b2) (L 0x100000000000a4fb2e6a2a5058e1c6e)))) (N (N (L 0x1000000000004fe24beb1e24334b9ac) (N (L 0x1000000000002650a6daf59fb68cde3) (L 0x1000000000001234e75169c7f34481a))) (N (L 0x10000000000008928e3e85186d3e49a) (N (L 0x100000000000040000d8fb5d31b17eb) (L 0x10000000000001d994fafca9f77747d)))))) (N (N (N (N (L 0x10000000000000d91d104c0f2b756bf) (N (L 0x1000000000000062ae59f3d4da6fc20) (L 0x100000000000002c78f54528f732dfe))) (N (L 0x1000000000000013e014365f92ac1ae) (N (L 0x1000000000000008cf3e60c527f3975) (L 0x1000000000000003df850c7f7d4354e)))) (N (N (L 0x1000000000000001b070f76d8bc6de7) (N (L 0x1000000000000000bb1e99adaabab40) (L 0x10000000000000005056af585acf6b5))) (N (L 0x1000000000000000223a827a235f6b4) (N (L 0x10000000000000000e7911bd6f8432f) (L 0x10000000000000000612ee6eba67625))))) (N (N (N (L 0x10000000000000000287c31a30f0c66) (N (L 0x1000000000000000010be2e83162e6e) (L 0x1000000000000000006dfda9dfbae80))) (N (L 0x1000000000000000002cd73c61f3455) (N (L 0x10000000000000000012270e98f7728) (L 0x100000000000000000074c398810e0d)))) (N (N (L 0x10000000000000000002e9f03174529) (N (L 0x1000000000000000000127d338797ac) (L 0x1000000000000000000074893b33c19))) (N (L 0x100000000000000000002d9ae4d6620) (N (L 0x1000000000000000000011bb1022fdd) (L 0x1000000000000000000006d95dcc767)))))))

private def cpos_lf_258 : FastDTree := dleaf cpos_bt_258 0xffffffffffb9cc7950103984582b39 0xffffffffff627b950c0230c3634fc8 0xffffffffffffa6f62ba009530f4481 0xfffffffffff06aa999db37176cd4c0 0xac73de605dc10fb8e6de 0xf9654fddcf0f8f77397 (M 0xffffffffffd4156773989a14449ea0 0xffffffffff59deaec4dae75e2b8f05 0x1000000000001c653879c5142ff0cdd 0xffffffffffefce23ee6cc3539debaf 0xfffffffffe575f4e23f0f443168c34 0x10000000000658f4f366eb953ba5f91 0x1000000000020dc284efd2089c46c62 0x100000000023c53091290b8d6c38bb7 0x104aae233e9ce327da1f (Q 0xabd636b2a87027d0b4dd 0x1b49aa2c0ee436497fe68 0x23d445466e114ee074bf1)) (M 0x1000000000008c2633b74411408e435 0xffffffffff55c979feee62755a2f48 0x100000000000657dda0284c4711df78 0xffffffffffef80d94cd8b97f053e93 0xfffffffffe64a65f5b75f0723f8e20 0xffffffffffded4e40da0a91519df28 0xffffffffff7cdde49d4658c75fd7b2 0x10000000001f3171c317a3f3f33b0ed 0x11ac983dbd433a465033 (Q 0xaa702f1ea7bfd5af23c2 0x19caf67df7f72f75fedd1 0x20407b27f4b244e62851d)) (M 0x100000000003975ff48f8359d00e34e 0xffffffffff6139eb04d2ee3748019d 0x100000000000b06190d719ca35100d0 0xfffffffffff082144f028b1c31eeda 0xfffffffffe94fb97bcbe21b5886994 0xffffffffff6e67cb1b9ea57aef9024 0xffffffffff0837c26e12b4b3799037 0x100000000018d02f27d1d384a0f9b16 0x130385c9baeb59cd4fac (Q 0xa8da030ba2f4376dd7a5 0x187202aecc64881cae4ac 0x1d3fd4efca5c82bdfe272)) (M 0x100000000006289140c43674fabb320 0xffffffffff790a4e636f0202165726 0x100000000000f6e9bd0982eeda7d4c4 0xfffffffffff2ce50bbe6914c4e5620 0xfffffffffedcd40ea3d2d4fad4760e 0xffffffffff19597e0e94e7048feb0b 0xfffffffffec00961b6b968e45a5117 0x100000000011a83c0ae9e69c46b612b 0x144db2fbda1fa75e5573 (Q 0xa71a5606685ef82599f7 0x1737513d8f7bdc4f94f5c 0x1aad6a6548e27cffe9ec8))

private def cpos_bt_260 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0x1000000000eb9e9435ff37d07341e37) (L 0x10000000070ee432b3582fe0a8ee75b))) (N (L 0x1000000025686a6f31d6066fbfc0c93) (N (L 0x10000000999998aa26cd42b5225cc39) (L 0x1000000207b9358d4f8a4de0c6848ca)))) (N (N (L 0x10000005e1fe48a07952e7d3e007dd9) (N (L 0x1000000efc711f2537451577334f736) (L 0x100000223446b6ba82327d2c53f709b))) (N (L 0x10000046f3dd87b69f286ca1a325b33) (N (L 0x100000874525f4ddc601fe05ad7ff8b) (L 0x100000ef25021a4241651471e0a1f47))))) (N (N (N (L 0x1000018aed576ea2c13a5fe12076f6e) (N (L 0x10000264edf0b37422b2e5a37cc118f) (L 0x100003829afa1bd871a68c91b59a4e7))) (N (L 0x100004e1f620f111db4e97faa65be7b) (N (L 0x10000677ea667f3b1224e6854facd7b) (L 0x100008302d87824ca56cc5f557587bc)))) (N (N (L 0x100009eee3a98921601b2fb54208121) (N (L 0x10000b93d4080e2313bc35459b3d32b) (L 0x10000cfe994f9f0cd271e0d5c62e5fc))) (N (L 0x10000e12fbee9bba91ffafd401320c1) (N (L 0x10000ebc9f8a5e087d6d7c523f7a962) (L 0x10000ef15c99a3ae89b4f260562c218)))))) (N (N (N (N (L 0x10000eb1f23dce3fcaec28f047cbd7e) (N (L 0x10000e0919777340e067ce5f2a635dd) (L 0x10000d095176fd01dc7d068002afc92))) (N (L 0x10000bc9ecaf4f230aee52016e1141b) (N (L 0x10000a63f20660e2ec455538cadf853) (L 0x100008ef51a8b994199ee685762ccb9)))) (N (N (L 0x10000780c4c9a8e18de86cfcad4fd26) (N (L 0x10000628803464048cefeae5fd49055) (L 0x100004f1b678aee4a60c5aa105e33d1))) (N (L 0x100003e2c71bf43e7146e32b08ae6aa) (N (L 0x100002fde75afe02bae2ee6936cf6f7) (L 0x100002420da120028009e9e8bb0b8db))))) (N (N (N (L 0x100001abef6ebd8fee855023d3887a0) (N (L 0x10000136eda3d0058314adcee963176) (L 0x100000ddd9060a61ce8ef5ce1c7ab09))) (N (L 0x1000009b857698033c1b363826571d8) (N (L 0x1000006b2bf8ab6a6b0ee8a4894de6a) (L 0x10000048a1e2040b528aba46b67b253)))) (N (N (L 0x100000306e9a064cb380ce3b660edf4) (N (L 0x1000001fc9e4c5af375ea2566c7f7e9) (L 0x100000148bb8f7238b22dbaf39a0e74))) (N (L 0x1000000d14d1a35171a59eecbefc899) (N (L 0x1000000835269384e7be7a5a9d63f70) (L 0x10000005139a83eec1effb884c620c7))))))) (N (N (N (N (N (L 0x1000000318addbf3ef8be9bd0425b22) (N (L 0x10000001dcee374bfac28f1d28f065e) (L 0x100000011b265e99babf9627e36e6e6))) (N (L 0x10000000a5ec6daa160c8b1badc7258) (N (L 0x100000005ffee443fddaa5d8667c094) (L 0x1000000036d930568392aabd2b5fe89)))) (N (N (L 0x100000001ef4f49d390df896f7144ea) (N (L 0x1000000011438d0baae246a88fd0187) (L 0x100000000983dac9af1d275202cfa26))) (N (L 0x10000000052f236314625db5467974e) (N (L 0x1000000002caf02dadb95ed36ae8ea5) (L 0x10000000017ce422a92962374ebd468))))) (N (N (N (L 0x1000000000c8b9b949c47169d9c90b0) (N (L 0x100000000068a7a59e68dec8ecadb5e) (L 0x100000000035fec26783f491d5eec38))) (N (L 0x10000000001b9270ca5baceced4fb4d) (N (L 0x10000000000deff3cf04d2471a23c1b) (L 0x100000000006f9aaef040255d7143ac)))) (N (N (L 0x10000000000374f713310f702691ded) (N (L 0x100000000001b260462facb8df65cd3) (L 0x100000000000d3327443c13a5fbccb5))) (N (L 0x10000000000065bb6e49da1a0f0e5e0) (N (L 0x100000000000308e467326f6ce31a7e) (L 0x10000000000016f77639f73c8f09020)))))) (N (N (N (N (L 0x1000000000000ac450b51479000cefe) (N (L 0x1000000000000500e4d19fb4d61a5a1) (L 0x100000000000024e210eefc64ef0af0))) (N (L 0x100000000000010d942f14364dfe59d) (N (L 0x100000000000007a1e71ed0e373a118) (L 0x1000000000000036dd49ac652816b1c)))) (N (N (L 0x100000000000001872ec1d0a546e5c8) (N (L 0x100000000000000aceced6e06676450) (L 0x1000000000000004bd6fb76ab7e3df7))) (N (L 0x1000000000000002100835aba3986fb) (N (L 0x1000000000000000e402a0a05ba5cc9) (L 0x100000000000000061b6072f21e5be8))))) (N (N (N (L 0x1000000000000000298f41e0e76e2da) (N (L 0x1000000000000000118bca8a346c5a6) (L 0x1000000000000000075a9013e35f62a))) (N (L 0x1000000000000000030f52d22cd901e) (N (L 0x100000000000000001439e6b0b40916) (L 0x10000000000000000084c26c27fe7d2)))) (N (N (L 0x1000000000000000003615a83d8bddc) (N (L 0x10000000000000000015e1e3af4116d) (L 0x10000000000000000008cb25b1155b4))) (N (L 0x1000000000000000000382945363a26) (N (L 0x10000000000000000001644ef9dc76b) (L 0x100000000000000000008c5c674adaa)))))))

private def cpos_lf_260 : FastDTree := dleaf cpos_bt_260 0xffffffffffcade3425bc7392100fec 0xffffffffff631ad005b95bcf518c13 0x100000000000142c3fb766abb4a65a1 0xfffffffffff2947fce109be418384b 0xa5a5ca46a6cde2b3b96d 0xd7aa1647af318489794 (M 0xffffffffffe5b34c211065edac9f0f 0xffffffffff5ceae415b7f577010c6e 0x100000000000340cac109ae20c86ac4 0xfffffffffff24013090dc5d88a4327 0xfffffffffe5160cd7896ccce5848f6 0x100000000003da136bbb485a9bdb43e 0xfffffffffff38a0975c19ed1d87219 0x100000000024bf1f2dcf31a11a96be9 0xe211a22dfad1f84265d (Q 0xa53080c400fd624fd52b 0x1b3027a3335b2b9c06aa7 0x24c13bfe67dfebe54e207)) (M 0x100000000001a64b426e2a0f184c4f5 0xffffffffff5dfee78574e0a42fa206 0x10000000000077157c96f226b845389 0xfffffffffff27f27cac9dec0ae23ec 0xfffffffffe6a8202b282d936a903ef 0xffffffffffb4ca5546de912e323506 0xffffffffff4c2e2c368977ea3e06db 0x10000000001f438e17aa913961c6ec0 0xf6b2a6611a71e0919c2 (Q 0xa423e2c1702bc71db55b 0x19c6873e81c51c092f71b 0x2138fad23e627c4f1a86f)) (M 0x10000000000499a6e1279d89389b066 0xffffffffff6ea1a3aae7fb56ac8223 0x100000000000b95d3f822ae007a10e8 0xfffffffffff3feb375b9d83bdade0e 0xfffffffffea6ef3a28a261786a2039 0xffffffffff45e8510f2b1390b96f0e 0xfffffffffed8ea4f4c9684c73b2bf0 0x100000000017fab30abd95fef883e7c 0x10aefc332b6c4ca1066a (Q 0xa2f0a8b12d193aa22a0d 0x1880bf69a7d509044a0b0 0x1e405782bd0f2586d6a8b)) (M 0x100000000006fb806e63421c47a839b 0xffffffffff8b3a94dc2315edb0530a 0x100000000000f4e01beb45f3d5c58dd 0xfffffffffff6b040305878a3dade71 0xfffffffffef9fc5390b9d1286c75a7 0xfffffffffef5dadc24c310acbcce77 0xfffffffffe965430a1a3f08194ee41 0x10000000001002e86e4040677bb9cb3 0x11ea2e2bdd36a16ac078 (Q 0xa19b39315675f8e8965e 0x17579fe8f56e4fa6e0846 0x1bb35c24172d3b7fb2d54))

private def cpos_bt_262 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0x1000000000fe7810b5325affd8a351c) (L 0x10000000082f93cbb9d7177c6aedff5))) (N (L 0x100000002e60fabdc1917ea1770cc79) (N (L 0x10000000cad2f19d2b9a9aee3dba61a) (L 0x10000002d8a31c6ef978676f18a4f08)))) (N (N (L 0x10000008bba5f05a0bfb63a3ae56ca0) (N (L 0x10000017804fd2a74ca10204b514cea) (L 0x100000388bc4708d706b5100dc26186))) (N (L 0x1000007b6d1ab00285ce88cf2b134e1) (N (L 0x100000f73136add10b927370b00b3f5) (L 0x100001ca631adbd492889184f705731))))) (N (N (N (L 0x10000318ebffb427476ca3b85e34061) (N (L 0x10000507699527ae85ca2f87ef587f3) (L 0x100007b443c862cdc90ce54269c8d16))) (N (L 0x10000b2f9d7d06ebcb0e6f8fb9344b7) (N (L 0x10000f73e36f7bc26399124f8508fc1) (L 0x10001460f44ece3e822f9a3f7dea20f)))) (N (N (L 0x100019bb80fc5b91abcbb902597dd0a) (N (L 0x10001f316280ef08b85f8cda761b434) (L 0x100024627ac75f74dc6c9e667f9fe5a))) (N (L 0x100028ec9cc5f1961f4d6dc0482054b) (N (L 0x10002c784198926a1c7d0181a97b299) (L 0x10002ec3aa1d8a1fb2e6843403557ae)))))) (N (N (N (N (L 0x10002faa79a2ccf2906fb845184ff21) (N (L 0x10002f28adb1a278f31ffdeda03e1f4) (L 0x10002d58d7f0b72a9965a44078e146e))) (N (L 0x10002a6e6642260a4878b89e549a5bc) (N (L 0x100026ad60d35f2f78c542b255fd212) (L 0x100022613fa91e6f5447ddbebd3df96)))) (N (N (L 0x10001dd4572d4e23da3d21991fca982) (N (L 0x10001948f7a1b7e9ff0bee6a4ff53d6) (L 0x100014f4d94b3ca37ccf94482f0a723))) (N (L 0x100010fef003b0573508b793873122c) (N (L 0x10000d7f5cb2182f7c9f728713e0a20) (L 0x10000a80f5be0dca72135056a872a40))))) (N (N (N (L 0x10000803c960a31a09e35f3954cfde6) (N (L 0x100006000632a27996a62b3f26a8bfd) (L 0x10000468d423437b6c4b616404c62ed))) (N (L 0x1000032ece85297c312f351ddd23e6f) (N (L 0x10000241f5c0c6dde1dbba426d6f8c5) (L 0x100001930e770f655a1f713d2f44280)))) (N (N (L 0x1000011479c2ea564ca7039f9cbfe8e) (N (L 0x100000ba9ebd93495a50382929c98bc) (L 0x1000007c0201927b544057078bfb831))) (N (L 0x1000005126e9ae83a055edbf4877710) (N (L 0x1000003452044533c685710092829a6) (L 0x100000213e923a353dbff84f042c262))))))) (N (N (N (N (N (L 0x10000014d344fee36251948d6e7ad9c) (N (L 0x1000000cdd93f3913f1a1f74051c098) (L 0x10000007d745381c5c606cbf6c2e5c6))) (N (L 0x10000004b72f7923849e7a5844a3faf) (N (L 0x10000002cca1e979a88c958e5b29e01) (L 0x10000001a40ab410251942d4fcdb827)))) (N (N (L 0x10000000f326b99ae9ab09b2b30ef33) (N (L 0x100000008b0bc6d34a3889b6ced3ce5) (L 0x100000004e91565ce4ebe3044b0cbd8))) (N (L 0x100000002be0785c20029ece8edb9a1) (N (L 0x1000000018391dd0df54934872e3ed6) (L 0x100000000d39077ed9168080ce05d79))))) (N (N (N (L 0x100000000723718c359075d55b4ca4b) (N (L 0x1000000003cfe4b5c280aebb4270d29) (L 0x1000000002039c83a3f5b63ed610eb8))) (N (L 0x10000000010d9441ffa016363408294) (N (L 0x10000000008b7fe4a7b77640ed3d430) (L 0x10000000004775976571319beb83dde)))) (N (N (L 0x1000000000243e176c17ee6fa9354ee) (N (L 0x10000000001233c2d5b0607ba7bc4a0) (L 0x1000000000090dd70b5b86675be1b82))) (N (L 0x100000000004760cfe80c700e014650) (N (L 0x1000000000022d7cae856b3c105abf1) (L 0x1000000000010da584507383bdddc64)))))) (N (N (N (N (L 0x100000000000813fbd07938cfa6f2c5) (N (L 0x1000000000003d67397d1ddbc2f20e2) (L 0x1000000000001cea9c0e8b02c4384b0))) (N (L 0x1000000000000d8015fb1cc4e0f41eb) (N (L 0x100000000000063fded8406dc68786d) (L 0x10000000000002de691abd7692b9ec0)))) (N (N (L 0x100000000000014e590a89ab9ecdbdd) (N (L 0x1000000000000096fa62a4ed246c4c8) (L 0x1000000000000043a1109ac401732c3))) (N (L 0x100000000000001e0de64bdc5f274f0) (N (L 0x100000000000000d407c28aaa71ec55) (L 0x1000000000000005cc57192e840a849))))) (N (N (N (L 0x1000000000000002848569d249836d6) (N (L 0x100000000000000115c2f20693dc073) (L 0x100000000000000076d140f625e76ba))) (N (L 0x100000000000000032746a02dc3ccb2) (N (L 0x100000000000000015453fecb919017) (L 0x100000000000000008e7389cbbcceaa)))) (N (N (L 0x100000000000000003b34bed80d56ec) (N (L 0x10000000000000000186faa19f4d968) (L 0x100000000000000000a04290dca4290))) (N (L 0x100000000000000000413e4fe1614e2) (N (L 0x1000000000000000001a6205244c27c) (L 0x1000000000000000000a990a646107f)))))))

private def cpos_lf_262 : FastDTree := dleaf cpos_bt_262 0xffffffffffd989a7d8ea6bc62d2e38 0xffffffffff65287de81ed823d9de0b 0x10000000000022045ad7bed2baa1053 0xfffffffffff471bcd339752e663c31 0x9f8c1b2df7ccd591563b 0xbbfea5c57f0e54ea06f (M 0xfffffffffff49fd40e44e9e282922a 0xffffffffff613c2f492d194c7dc4ac 0x1000000000003fa0507e751868ebdf2 0xfffffffffff4554a95bcb09a0c345e 0xfffffffffe5009c25bb89c787329c1 0x1000000000018a063eafbc43c078b3f 0xffffffffffc71403b7cda9fd9b1fee 0x10000000002560e9583e1ea8fea431c 0xc5370978acb6248f3db (Q 0x9f2c03494293ec3c6cef 0x1b0a9ce30f2d02fa04118 0x258c27cc0cc170803b259)) (M 0x1000000000028c628b8252b74c78a43 0xffffffffff670594b2605865742f10 0x1000000000007c8131564e4208ac2c9 0xfffffffffff4fd1652cdb2f3207324 0xfffffffffe749df708afde81f7ba54 0xffffffffff8f0fedf833e78a9bb3af 0xffffffffff1dded181a66315851456 0x10000000001efd7a4a0c6a3cb4a027e 0xd7bc249b085665e7083 (Q 0x9e519f78c2254993c399 0x19b3252996083eaebd7b4 0x220f8c72360128aa0ed6f)) (M 0x1000000000056018687f9133db51560 0xffffffffff7c3af6cf18f3e3db660f 0x100000000000b6857c1ef822e4513cf 0xfffffffffff6d37a79397dd820477f 0xfffffffffebc59cd69c9d779714f34 0xffffffffff230e7cbd3ac02ffa482a 0xfffffffffead857a71e32b71eea8bc 0x100000000016d3ce6f65e099c5c81f5 0xea3872a43cf7e991962 (Q 0x9d5a9e01dd707858fccb 0x187df9ac37d741cec72ac 0x1f1f65bdd64106bf0f9a4)) (M 0x1000000000078cc5b9d668b58672067 0xffffffffff9cd464bb4a871a0743c1 0x100000000000e7e164cf921723717c3 0xfffffffffff9c04bb6f0297e69771b 0xffffffffff1972f27ad0c89c2febff 0xfffffffffed92e9f24e4ca16d1f0ae 0xfffffffffe71f3cef8e7f91004b6ba 0x10000000000e19b3a51d7bdf47cd105 0xfc84607be09ba220243 (Q 0x9c4a94b630f307e1ea4f 0x17642d552bd976ab999fb 0x1c9897b884aacf482d76f))

private def cpos_bt_264 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0x100000000111518d34657e2f3e04c02) (L 0x1000000009667849234c10e9147758f))) (N (L 0x1000000038bab959d59625590bd9c42) (N (L 0x10000001076b56c42a38f8eea4b7f00) (L 0x10000003ea14868d7a7160dfbe8175c)))) (N (N (L 0x1000000cb01ea40b2f0ff3fbb08a03a) (N (L 0x10000023feeb4d8712177bb7ef01de3) (L 0x1000005b22c35a5906a1a7db1043bdd))) (N (L 0x100000d0f9c53f3b2f1ad14e7686927) (N (L 0x100001b700c5a4cd79ceb5bd9fedb59) (L 0x10000354ba6d402f717a4c762ec2d8c))))) (N (N (N (L 0x1000060723d95a921feffcacda052ba) (N (L 0x10000a3a15c227712d73885fd8ac697) (L 0x1000105a88717607a2d192dee1223d2))) (N (L 0x100018c296d5f660256a52bbfc6e949) (N (L 0x100023a252d3f63f3deb7c69cfbf507) (L 0x100030ea44e22962759212318970768)))) (N (N (L 0x1000403d1494a9e357a562eca68af69) (N (L 0x100050ecf2e87752dcea913cc9c90a0) (L 0x100062070e945d17cd26a9c9125849f))) (N (L 0x1000726c37fd5d7581bfe46613612f3) (N (L 0x100080f2c83101bb1e1316c491b88a6) (L 0x10008c8bb9af77639c2204f33458a01)))))) (N (N (N (N (L 0x100094643a3cc61f58333c0de94163b) (N (L 0x100097fdeb9801e015bba26b6f03437) (L 0x1000973a33cccbc6afbce6226570f5c))) (N (L 0x10009257bf2a40473f01cc083f3322e) (N (L 0x100089e3f5fd27cff5d22123b78f7a0) (L 0x10007ea412c7ea067b45e888a0eb87e)))) (N (N (L 0x1000717a6bd209a668706a3eae26f49) (N (L 0x1000634c61ff9708c3237dcbab7b1e6) (L 0x100054ec798c0e1c3fa6bd8f4f7298e))) (N (L 0x1000470ac31b40f41f6d4a3df89968b) (N (L 0x10003a2c4b4e239852006cbc2417dc5) (L 0x10002ea90f9d290800051511fc5a315))))) (N (N (N (L 0x100024af241b2e328014a398f277445) (N (L 0x10001c4952228069473f30dad39283e) (L 0x1000156775c4bbde420359ffc6871aa))) (N (L 0x10000fe72298f5002248c1a90ccf74d) (N (L 0x10000b9b7f9e1d0f980987753e7ea0c) (L 0x10000853b8a57bd3e4e0df9233fa58f)))) (N (N (L 0x100005dfc5a10293b24e18925802b3b) (N (L 0x10000413921b13b684714045a5a127d) (L 0x100002c8bdf81a9530f87a2ac710b8f))) (N (L 0x100001df470c1b8998425e6442a365b) (N (L 0x1000013d6eb6b76f787819cbff42661) (L 0x100000cf262de1ff6a717a41c839c5a))))))) (N (N (N (N (N (L 0x100000853d53aeb5e9af5169bd91330) (N (L 0x100000547f7392ed2a08e1c14e9b67e) (L 0x10000034da067b34ba2091ba3f3020a))) (N (L 0x100000209d2fb463455a22aef0a58d7) (N (L 0x10000013dc823a774d4abd9d5b4fd4f) (L 0x1000000bf0928befaf48759f939e508)))) (N (N (L 0x1000000716564acb59261d864b7f91d) (N (L 0x1000000427ae16d87fb8308e7fe22f0) (L 0x10000002680ede104effc0d9e052c61))) (N (L 0x100000016093a8780f63132e5abd274) (N (L 0x10000000c7700a24236b862a5c9b463) (L 0x100000006f86cc7be16e1f19d4b7aa4))))) (N (N (N (L 0x100000003dab0372fcff82c6629b57f) (N (L 0x1000000021b96682f0ce42fe6c5b9a6) (L 0x10000000123e5c859e3381a7ba9c678))) (N (L 0x1000000009c3b55d5568a1cc9acba67) (N (L 0x10000000052bf930b7877650c62a5cd) (L 0x1000000002b60fe1dd645d46d48eea1)))) (N (N (L 0x1000000001682e9883c8045b54d23b2) (N (L 0x1000000000b9109080a56ca0fc2278c) (L 0x10000000005e295f1b89deba9558050))) (N (L 0x10000000002f7358bff905ac793fb26) (N (L 0x100000000017afa2038d05e4e270dde) (L 0x10000000000bb6b2c759aa20056f5ed)))))) (N (N (N (N (L 0x100000000005bd6991267f927e466eb) (N (L 0x100000000002c98da420499d6b1402c) (L 0x100000000001576e6e11bf092499b44))) (N (L 0x100000000000a3d923a445c0277ec53) (N (L 0x1000000000004d7f575e6fafd8f06ef) (L 0x100000000000245806b3e5988cf46d2)))) (N (N (L 0x10000000000010e6c9109ddc2b8bc62) (N (L 0x10000000000007cb8bdac13ab80caf9) (L 0x1000000000000390df63844eba99dff))) (N (L 0x100000000000019e3f26655d0708eca) (N (L 0x10000000000000ba7d74c29507259e8) (L 0x10000000000000534cdc77776e45d3f))))) (N (N (N (L 0x1000000000000024ebd2ad24337fc2d) (N (L 0x10000000000000103d747421583e7af) (L 0x100000000000000716f35dd081f3a38))) (N (L 0x100000000000000312723e9d1d368bf) (N (L 0x10000000000000015248978aa471e58) (L 0x100000000000000090751cd548ceb00)))) (N (N (L 0x10000000000000003d3f3e2c60cfde0) (N (L 0x100000000000000019c8c2de4d1e33c) (L 0x10000000000000000ac775228731a5a))) (N (L 0x10000000000000000479a542ec59615) (N (L 0x100000000000000001d86624412716e) (L 0x100000000000000000c17aac53adbd4)))))))

private def cpos_lf_264 : FastDTree := dleaf cpos_bt_264 0xffffffffffe6481382eb703dd03412 0xffffffffff67f5debb71c3b409b6f3 0x100000000000299736cc80500649502 0xfffffffffff5d8a0a295701862de3f 0x9a330eb769820409b480 0xa7b33829a4f4a8e73db (M 0x1000000000001653431c238566a9c7b 0xffffffffff6622289b95853eaaecd7 0x10000000000044ecd95d608c5c23db7 0xfffffffffff5e7637f33237bd4b6cf 0xfffffffffe5241a5f8417b14ea4f75 0xfffffffffff69b21386a4c399e47a6 0xffffffffff9c085eaad2dff6f8ad7f 0x100000000025b746da7461a94973b7f 0xafa0d8e354f2058eaf7 (Q 0x99df764372595808baeb 0x1add8a2612e23b0fcbeb3 0x263add0e7abd2ec278db4)) (M 0x10000000000349616d447f1766557a8 0xffffffffff702ebff6646a789177af 0x1000000000007be2442cd38bdb1c673 0xfffffffffff6dc410e71c9a9ec3cc8 0xfffffffffe81c220e47278a47b2506 0xffffffffff6d7afd0b581ab220b526 0xfffffffffef25bedf9ab4307d82c33 0x10000000001e6ef23ad0bbe1a95a6ed 0xbfa7b17c92b03cc67c8 (Q 0x99213f829d1b975d5619 0x1995c7ff67c900de05ebe 0x22c9b540deb9342b7433a)) (M 0x100000000005f83175420f051ecfe7b 0xffffffffff8960a34c83fd05ee66b4 0x100000000000ae43a56ebd937521de0 0xfffffffffff8ebdd3303902b86ed8c 0xfffffffffed3eddc2b61a3be86b053 0xffffffffff056b30dda1c3ecc1f464 0xfffffffffe8645ccb8431353091191 0x1000000000156de7d4c1e4f2f45f669 0xcfd5dbfbf98f256201d (Q 0x984b98970cdf8bbbec34 0x186f073619f78701890e1 0x1fe226c454e29a5d684ff)) (M 0x100000000007ec835a667ec513c928f 0xffffffffffad452a69304a68c91b14 0x100000000000d68c21c72f12ddf1d10 0xfffffffffffbf59b58b011b7763ade 0xffffffffff39e29374e27e4c3a2018 0xfffffffffec297a57fc6c71f357940 0xfffffffffe52e8dd8bcce9990b5a2e 0x10000000000c011c5243899ac13cc7f 0xe01387ce6e187a07fe8 (Q 0x9762fb84bb20d35f72bb 0x1762973147dd51c15d48c 0x1d61dbd13deedce601a0b))

private def cpos_bt_266 : BTree := N (N (N (N (N (N (L 0x1000000000100000000000000000000) (N (L 0x1000000001242b09b398a15ea3662e8) (L 0x100000000ab391aaefb71c26a58a823))) (N (L 0x10000000448fcf9e812bc5252644416) (N (L 0x1000000151124607e61fe1f5585ae44) (L 0x100000054a6e18068bc3ddb100ca39a)))) (N (N (L 0x1000001213b426fab3829ed9cc954f8) (N (L 0x10000035f570ef1b98f0f8594876e80) (L 0x1000008f8038d838d65914ab0ad5b5d))) (N (L 0x100001591d397df6e71dd5e5e671f5e) (N (L 0x100002f758c410298d17b3bd4aa4736) (L 0x10000606eaaf818b2cfee22d97ef54d))))) (N (N (N (L 0x10000b6561587c0411adb418f7561b5) (N (L 0x1000142e158bc40cb16d07e662d96fd) (L 0x100021a5b219d0fd7059fcfa39c8e83))) (N (L 0x10003511ae43a36282780a957d60cec) (N (L 0x10004f7e4aeecb688ace47fa361b039) (L 0x1000717ba28f432a137b57cd35b2531)))) (N (N (L 0x10009adf3c1f1b7a6bab2acb504399b) (N (L 0x1000ca9970523e389b4701e3daf75c3) (L 0x1000feabb782290418c59555a3b5160))) (N (L 0x10013446d92279e836bbe0afcfe505b) (N (L 0x1001680f70588fea3c8385e177e4eb7) (L 0x1001967e9acc1e9f24a266fc5004108)))))) (N (N (N (N (L 0x1001bc4e499ed8537ec6953fde2442b) (N (L 0x1001d6de366c0b71baf2c097d07a0e3) (L 0x1001e48067c9c57bd2ea29056e4a222))) (N (L 0x1001e4a1b96fdcf7855c6d8b6aa3a83) (N (L 0x1001d7ca61f51842f8bc4959737981d) (L 0x1001bf7a00811fa7ecb910a58c18290)))) (N (N (L 0x10019de8a788c5a18f74e7c240907af) (N (L 0x100175b9974c8f3ff6dec25d7124d7e) (L 0x100149acb193312a13a7027da71866e))) (N (L 0x10011c599949473d0d0c8a1b7568e43) (N (L 0x1000effbd4f76ab9a19b9fb76122839) (L 0x1000c6533212799b9dc862a4dcd695b))))) (N (N (N (L 0x1000a097f3bb6dc984b36c51454997f) (N (L 0x10007f7f9e2d06c77a9af99463c6519) (L 0x1000634dac1edbbb18032793cd97450))) (N (L 0x10004beb1b8822f38e4adeb95a0f59d) (N (L 0x100039003fd5ea61c2f6cd7711875b2) (L 0x10002a0d503210e968e46b748f08d4f)))) (N (N (L 0x10001e7f63823cda677c8962a6e02d3) (N (L 0x100015c0b6c2586455bb460ea266a25) (L 0x10000f440bdd55656b20dcbbacfdb58))) (N (L 0x10000a8b95cf99630ba040055bdb95b) (N (L 0x1000072c43f6dfa8792989903700e24) (L 0x100004ce5ecec390d592282d0e192c9))))))) (N (N (N (N (N (L 0x1000032c5dbd1608a576ac45b39ed0d) (N (L 0x10000210b9bce6e46e0d96cd108ac03) (L 0x1000015352642e0fa9840bf3f587955))) (N (L 0x100000d6cc647655801d8feae683b98) (N (L 0x10000086287d5b9487b1cdc30c4a939) (L 0x10000052b2a10551b0af63940f13246)))) (N (N (L 0x100000325316e891ec03833bc6d5ffd) (N (L 0x1000001e3d96db2760f975741026fe7) (L 0x10000011f2e0b300ea83b0280ea26c5))) (N (L 0x1000000a865ec5fc436745f610ae78c) (N (L 0x100000061948adf166047592ea0c40a) (L 0x100000037e3922c05c5ed7cbfa4d747))))) (N (N (N (L 0x10000001fa5791db91b329e4e00e100) (N (L 0x100000011b82663f11a542906175c32) (L 0x100000009d006d8048a3e4c5c42f44c))) (N (L 0x1000000056021738b96b0575609c94e) (N (L 0x100000002e9e456c4b1c05fdd9cfa59) (L 0x1000000019015d3190c0dbce8071b8e)))) (N (N (L 0x100000000d467e6e3a9fa5025cf6d6e) (N (L 0x1000000006fa2078bfdec9d18cdc1d3) (L 0x1000000003a1710b0799e24d1833fcc))) (N (L 0x1000000001def1f631bb85e7d575a16) (N (L 0x1000000000f4707a78a796a03e58c10) (L 0x10000000007b942ae46b2d134803769)))))) (N (N (N (N (L 0x10000000003de590f972d0e5abbedc4) (N (L 0x10000000001eb80590d87981afb6bfd) (L 0x10000000000f1bb7c7060e8063eb726))) (N (L 0x1000000000075d5e809ffd859e70cab) (N (L 0x1000000000038f043cd6d78df6b9663) (L 0x100000000001b46a36701ca35bcb6a0)))) (N (N (L 0x100000000000cf4935e2d31a157e1f6) (N (L 0x10000000000061a1a3e56f1f5e6c972) (L 0x1000000000002d9acb056601427dafe))) (N (L 0x100000000000152104715565bb508e3) (N (L 0x10000000000009b5e8b47ec3565cb03) (L 0x100000000000046d6f649c8d0391436))))) (N (N (N (L 0x1000000000000200bdcf6b6622a0507) (N (L 0x10000000000000e629ab02c89405dd0) (L 0x100000000000006687a0454151060e8))) (N (L 0x100000000000002d547b867831b63bc) (N (L 0x1000000000000013e469cf6d9c99a77) (L 0x1000000000000008aa51abaf3d338ee)))) (N (N (L 0x1000000000000003bf537c7f05e0a0d) (N (L 0x10000000000000019be5b46338789da) (L 0x1000000000000000af9a1fd26db9936))) (N (L 0x10000000000000004a57250acd649c5) (N (L 0x10000000000000001f411f40883baa0) (L 0x10000000000000000d0ce4a641b0822)))))))

private def cpos_lf_266 : FastDTree := dleaf cpos_bt_266 0xfffffffffff1984e6e14e59ac93d7a 0xffffffffff6b43b484211af12f3433 0x100000000000303ec84789c3e25473c 0xfffffffffff6ea2d70649dbb17107f 0x956e742a02ed45046c85 0x992937699439530db3e (M 0x100000000000c8f96710ead351cd2fb 0xffffffffff6b5e7d603a94093fbaec 0x1000000000004966416d30bda4e8fef 0xfffffffffff71a3aa273f16db17be3 0xfffffffffe572d902dbcef41e22df9 0xffffffffffd777a635bd73c30722be 0xffffffffff72be337715714bab62ef 0x100000000025cdb299cb2dcf93745b3 0xa02b3b4fe1ea5d1f27d (Z (Q 0x9501a292f0540f493433 0x1a74e133802642d290e41 0x26d21b04756c1b4cb1485) (Q 0x954f2e7b0988f4f68936 0x1b1a8bfa64f29d2d6235e 0x26d21b04756c1b4cb1485))) (M 0x100000000003e7d35893b7f56c82b57 0xffffffffff7942601ee7ddb8df6bbb 0x1000000000007ad90ccd3900761d813 0xfffffffffff84723acf8f3da98c43b 0xfffffffffe910216b0ac9d6cb78c19 0xffffffffff4fbf32f6d9325c3d8d96 0xfffffffffec9d8897d32f1f1368139 0x10000000001da5b070c667c7d30d96c 0xae3baaae2b79d3db6be (Q 0x9486a31889cd117b4a05 0x1971f2ff9df3ebf3591f2 0x236c0bc27b196dd4e20fe)) (M 0x1000000000066e5f5851922d381bfe8 0xffffffffff95e7c20f4b1e8354c856 0x100000000000a6563514404fddb1eca 0xfffffffffffa7a2e65a516353a14c0 0xfffffffffeecb7e6ee139c98497340 0xfffffffffeec77649ac183796d5479 0xfffffffffe632f2ddaeacc67e68b93 0x100000000013d88a96e84ea14180440 0xbc59d85d41492887eb7 (Q 0x93cc31edd29a61199762 0x1857c3929539cd789fcd8 0x208cfba228a29c4f047c0)) (M 0x100000000008290a0e08d1de624943c 0xffffffffffbc76dfe7345daa8e37ab 0x100000000000c6a9912e309c89b0cd9 0xfffffffffffd8b84983dcfb39961cf 0xffffffffff5a5da658122725f00222 0xfffffffffeb14e1b9985aafee50786 0xfffffffffe38fe8bf00ee6fe281f24 0x100000000009c9ddc08c59d4a9d3f56 0xca822d82b8cbddc8ed4 (Q 0x92ff5dcf9ec07c7dce39 0x1756fed870205002051c0 0x1e134a9e5c6004092420f))

private def cpos_sub_30 : FastDTree := (dsplit (dsplit (dsplit cpos_lf_252 cpos_lf_254) (dsplit cpos_lf_256 cpos_lf_258)) (dsplit (dsplit cpos_lf_260 cpos_lf_262) (dsplit cpos_lf_264 cpos_lf_266)))

private def cpos_node_31 : FastDTree := dsplit cpos_node_29 cpos_sub_30

private theorem cpos_ok_27 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f false cpos_sub_27 0 2 = true := by
  decide

private theorem cpos_ok_28 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f false cpos_sub_28 1 2 = true := by
  decide

private theorem cpos_nok_29 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f false cpos_node_29 0 1 = true := by
  rw [show cpos_node_29 = dsplit cpos_sub_27 cpos_sub_28 from rfl]
  exact checkFastDTree_dsplit _ _ _ _ _ _ _ _ _ _ cpos_sub_27 cpos_sub_28 0 1 0 1 2 rfl rfl rfl cpos_ok_27 cpos_ok_28

private theorem cpos_ok_30 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f false cpos_sub_30 1 1 = true := by
  decide

private theorem cpos_nok_31 :
  checkFastDTree 0x100000000000000000000 0x1000000000000000000000000000000 0x174876e800 0x1b6e01bc5da 0x12d97c7f33232f65616e5c 0x540540540540540541 0xaec33e1f671529a49 0x346dc5d63886594b0 0x68db8bac710cb295f false cpos_node_31 0 0 = true := by
  rw [show cpos_node_31 = dsplit cpos_node_29 cpos_sub_30 from rfl]
  exact checkFastDTree_dsplit _ _ _ _ _ _ _ _ _ _ cpos_node_29 cpos_sub_30 0 0 0 1 1 rfl rfl rfl cpos_nok_29 cpos_ok_30

end GaussSmallBridge

theorem solution (δ : ℝ) (hd_lo : 0 ≤ δ) (hd_hi : δ ≤ 1) {t : ℝ}
    (hlo : -(23 / 16) ≤ t) (hhi : t ≤ -1) :
    ‖mellin (fun u : ℝ => (Real.exp (-u ^ 2 / 2) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ)))
      ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖mellin (fun u : ℝ => (Real.exp (-u ^ 2 / 2) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ)))
        ((1 / 2 : ℂ) - Complex.I)‖ := by
  apply GaussSmallBridge.sound_subtree_lit false GaussSmallBridge.cpos_node_31
    0 0 (by norm_num) GaussSmallBridge.cpos_nok_31 δ _ hlo hhi
  rw [abs_le]; norm_num [GaussSmallBridge.signB]; constructor <;> linarith

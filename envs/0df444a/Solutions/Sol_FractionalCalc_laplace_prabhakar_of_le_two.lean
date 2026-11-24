-- Prove2me | solution 1 for FractionalCalc.laplace_prabhakar_of_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T07:57:25.088679+00:00
-- url     : https://prove2.me/submissions/d633c49c-2452-4c83-9f43-101a6b4d413e

import Mathlib
import Definitions.Def_FractionalCalc_mittagLeffler
import Definitions.Def_QueueingFundamentals_Transient_laplace
set_option autoImplicit false
open MeasureTheory Set Classical QueueingFundamentals.Transient
open Filter Topology FractionalCalc

namespace FractionalCalc
theorem fc2_choose_neg (γ : ℝ) (k : ℕ) :
    Ring.choose (-γ) k * (k.factorial : ℝ) = (-1) ^ k * ∏ j ∈ Finset.range k, (γ + j) := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose (-γ) k
  rw [← Polynomial.aeval_eq_smeval, ← Polynomial.eval_map_algebraMap, descPochhammer_map,
    descPochhammer_eval_eq_prod_range, nsmul_eq_mul] at h
  rw [mul_comm, ← h, show ((-1 : ℝ) ^ k) = (-1) ^ (Finset.range k).card by simp,
    ← Finset.prod_neg]
  refine Finset.prod_congr rfl fun j _ => ?_
  ring

theorem fc2_hasSum_binom (γ : ℂ) (w : ℂ) (hw : ‖w‖ < 1) :
    HasSum (fun n : ℕ => Ring.choose (-γ) n * w ^ n) ((1 + w) ^ (-γ)) := by
  have hw' : w ∈ Metric.eball (0 : ℂ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff,
      ← NNReal.coe_lt_coe]
    simpa using hw
  have h := (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := -γ)).hasSum hw'
  simpa [binomialSeries, FormalMultilinearSeries.ofScalars, List.prod_ofFn] using h

theorem fc2_summable_binom (γ : ℂ) (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable (fun n : ℕ => ‖Ring.choose γ n‖ * ρ ^ n) := by
  have h1' : (ρ.toNNReal : ENNReal) < 1 := by
    rw [← ENNReal.coe_one, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ h0]
    exact h1
  have h := (binomialSeries ℂ γ).summable_norm_mul_pow
    (lt_of_lt_of_le h1' binomialSeries_radius_ge_one)
  simpa [binomialSeries, FormalMultilinearSeries.ofScalars_norm, Real.coe_toNNReal _ h0] using h

theorem fc2_real_int (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-(r * t))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr]
  have := Real.Gamma_pos_of_pos ha
  positivity

theorem fc2_meas (a : ℝ) (s : ℂ) :
    Measurable (fun t : ℝ => Complex.exp (-s * t) * ((t ^ (a - 1) : ℝ) : ℂ)) := by
  fun_prop

theorem fc2_norm_eq (a : ℝ) (s : ℂ) (t : ℝ) (ht : 0 < t) :
    ‖Complex.exp (-s * t) * ((t ^ (a - 1) : ℝ) : ℂ)‖ = t ^ (a - 1) * Real.exp (-(s.re * t)) := by
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  simp [mul_comm]

theorem fc2_cint (a : ℝ) (ha : 0 < a) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s * t) * ((t ^ (a - 1) : ℝ) : ℂ)) (Ioi 0) := by
  refine Integrable.mono' (fc2_real_int a s.re ha hs) (fc2_meas a s).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
  exact (fc2_norm_eq a s t ht).le

theorem fc2_norm_int (a : ℝ) (ha : 0 < a) (s : ℂ) (hs : 0 < s.re) :
    ∫ t in Ioi (0 : ℝ), ‖Complex.exp (-s * t) * ((t ^ (a - 1) : ℝ) : ℂ)‖ =
      (1 / s.re) ^ a * Real.Gamma a := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => fc2_norm_eq a s t ht)]
  exact Real.integral_rpow_mul_exp_neg_mul_Ioi ha hs

theorem fc2_lap_diff (a : ℝ) (ha : 0 < a) (s₀ : ℂ) (hs : 0 < s₀.re) :
    DifferentiableAt ℂ
      (fun s : ℂ => ∫ t in Ioi (0 : ℝ), Complex.exp (-s * t) * ((t ^ (a - 1) : ℝ) : ℂ)) s₀ := by
  set ε := s₀.re / 2 with hε
  have hε0 : 0 < ε := by positivity
  have hbound_int : IntegrableOn
      (fun t : ℝ => t ^ (a - 1) * t * Real.exp (-(ε * t))) (Ioi 0) := by
    refine (fc2_real_int (a + 1) ε (by linarith) hε0).congr ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    simp only
    rw [show a + 1 - 1 = (a - 1) + 1 by ring, Real.rpow_add_one (ne_of_gt ht)]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (s : ℂ) (t : ℝ) => Complex.exp (-s * t) * ((t ^ (a - 1) : ℝ) : ℂ))
    (F' := fun (s : ℂ) (t : ℝ) => Complex.exp (-s * t) * (-(t : ℂ)) * ((t ^ (a - 1) : ℝ) : ℂ))
    (x₀ := s₀) (s := Metric.ball s₀ ε)
    (bound := fun t : ℝ => t ^ (a - 1) * t * Real.exp (-(ε * t)))
    (Metric.ball_mem_nhds s₀ hε0)
    (Eventually.of_forall fun s => (fc2_meas a s).aestronglyMeasurable)
    (fc2_cint a ha s₀ hs)
    (by fun_prop)
    ?_ hbound_int ?_
  · exact key.2.differentiableAt
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht z hz => ?_
    have ht' : (0 : ℝ) < t := ht
    have hzre : ε < z.re := by
      have h1 := Complex.abs_re_le_norm (z - s₀)
      rw [Metric.mem_ball, dist_eq_norm] at hz
      rw [Complex.sub_re] at h1
      linarith [(abs_lt.mp (h1.trans_lt hz)).1]
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg ht'.le _), Real.norm_of_nonneg ht'.le]
    have : Real.exp (-z * (t : ℂ)).re ≤ Real.exp (-(ε * t)) := by
      apply Real.exp_le_exp.mpr
      simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
      nlinarith
    calc Real.exp (-z * (t : ℂ)).re * t * t ^ (a - 1)
        ≤ Real.exp (-(ε * t)) * t * t ^ (a - 1) := by gcongr
      _ = t ^ (a - 1) * t * Real.exp (-(ε * t)) := by ring
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht z hz => ?_
    have h1 : HasDerivAt (fun z : ℂ => -z * (t : ℂ)) (-(t : ℂ)) z := by
      simpa using ((hasDerivAt_id z).neg.mul_const (t : ℂ))
    exact h1.cexp.mul_const _

theorem fc2_lap_real (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 0 < r) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-(r : ℂ) * t) * ((t ^ (a - 1) : ℝ) : ℂ) =
      Complex.Gamma a * (1 / (r : ℂ)) ^ (a : ℂ) := by
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := (a : ℂ)) (by simpa using ha) hr
  rw [mul_comm, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [Complex.ofReal_cpow (le_of_lt ht), mul_comm]
  push_cast
  ring_nf

theorem fc2_lap (a : ℝ) (ha : 0 < a) (s : ℂ) (hs : 0 < s.re) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-s * t) * ((t ^ (a - 1) : ℝ) : ℂ) =
      Complex.Gamma a * (1 / s) ^ (a : ℂ) := by
  set U : Set ℂ := {z | 0 < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hF : AnalyticOnNhd ℂ
      (fun s : ℂ => ∫ t in Ioi (0 : ℝ), Complex.exp (-s * t) * ((t ^ (a - 1) : ℝ) : ℂ)) U :=
    DifferentiableOn.analyticOnNhd
      (fun z hz => (fc2_lap_diff a ha z hz).differentiableWithinAt) hUo
  have hG : AnalyticOnNhd ℂ (fun s : ℂ => Complex.Gamma a * (1 / s) ^ (a : ℂ)) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUo
    have hz' : (0 : ℝ) < z.re := hz
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz'
    refine (differentiableAt_const _).mul ?_ |>.differentiableWithinAt
    refine (differentiableAt_const _ |>.div differentiableAt_id hz0).cpow
      (differentiableAt_const _) ?_
    left
    show 0 < (1 / z).re
    simp only [one_div, Complex.inv_re]
    exact div_pos hz' (Complex.normSq_pos.mpr hz0)
  have h1 : (1 : ℂ) ∈ U := by simp [hU]
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ),
      (∫ t in Ioi (0 : ℝ), Complex.exp (-z * t) * ((t ^ (a - 1) : ℝ) : ℂ)) =
        Complex.Gamma a * (1 / z) ^ (a : ℂ) := by
    have htend : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have := (Complex.continuous_ofReal.tendsto (1 : ℝ))
        simpa using this.mono_left nhdsWithin_le_nhds
      · refine eventually_nhdsWithin_of_forall fun x hx => ?_
        simpa using hx
    refine htend.frequently ?_
    have hev : ∀ᶠ x in 𝓝[≠] (1 : ℝ), 0 < x :=
      nhdsWithin_le_nhds (lt_mem_nhds one_pos)
    refine hev.frequently.mono fun x hx => ?_
    exact fc2_lap_real a ha x hx
  have := hF.eqOn_of_preconnected_of_frequently_eq hG
    (convex_halfSpace_re_gt 0).isPreconnected h1 hfreq
  exact this hs

theorem fc2_mul_cpow (x y z : ℂ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : Complex.arg x + Complex.arg y ∈ Ioc (-Real.pi) Real.pi) :
    (x * y) ^ z = x ^ z * y ^ z := by
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hx hy), Complex.cpow_def_of_ne_zero hx,
    Complex.cpow_def_of_ne_zero hy, (Complex.log_mul_eq_add_log_iff hx hy).mpr h, add_mul,
    Complex.exp_add]

theorem fc2_arg_sum (u b : ℂ) (hu0 : u ≠ 0) (hu : |Complex.arg u| < Real.pi) (hb : 0 < b.re)
    (him : (u * b).im = u.im) :
    Complex.arg u + Complex.arg b ∈ Ioc (-Real.pi) Real.pi := by
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  have hbarg : |Complex.arg b| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb)
  have hpi := Real.pi_pos
  have hub : Complex.arg (u * b) =
      ((Complex.arg u + Complex.arg b : ℝ) : Real.Angle).toReal := by
    rw [Real.Angle.coe_add, ← Complex.arg_mul_coe_angle hu0 hb0,
      Complex.arg_coe_angle_toReal_eq_arg]
  have hua := Complex.arg_mem_Ioc u
  rw [abs_lt] at hu hbarg
  rcases lt_trichotomy u.im 0 with h | h | h
  · have h1 : Complex.arg u < 0 := Complex.arg_neg_iff.mpr h
    have h2 : Complex.arg (u * b) < 0 := Complex.arg_neg_iff.mpr (by rw [him]; exact h)
    refine ⟨?_, by linarith⟩
    by_contra hc
    push Not at hc
    rw [Real.Angle.toReal_coe_eq_self_add_two_pi_iff.mpr ⟨by linarith, hc⟩] at hub
    linarith
  · have h1 : Complex.arg u = 0 := by
      refine Complex.arg_eq_zero_iff.mpr ⟨?_, h⟩
      by_contra hc
      push Not at hc
      have := Complex.arg_eq_pi_iff.mpr ⟨hc, h⟩
      linarith
    rw [h1]
    constructor <;> linarith
  · have h1 : 0 ≤ Complex.arg u := Complex.arg_nonneg_iff.mpr h.le
    have h2 : 0 ≤ Complex.arg (u * b) := Complex.arg_nonneg_iff.mpr (by rw [him]; exact h.le)
    refine ⟨by linarith, ?_⟩
    by_contra hc
    push Not at hc
    rw [Real.Angle.toReal_coe_eq_self_sub_two_pi_iff.mpr ⟨hc, by linarith⟩] at hub
    linarith

theorem fc2_alg (α β γ c : ℝ) (s : ℂ) (hα : 0 < α) (hα2 : α ≤ 2) (hs : 0 < s.re)
    (hw : ‖(c : ℂ) * (1 / s) ^ (α : ℂ)‖ < 1) :
    (1 / s) ^ (β : ℂ) * (1 + c * (1 / s) ^ (α : ℂ)) ^ (-(γ : ℂ)) =
      s ^ (α * γ - β : ℂ) / (s ^ (α : ℂ) + c) ^ (γ : ℂ) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hsarg : |Complex.arg s| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hs)
  have hpi := Real.pi_pos
  have hsπ : Complex.arg s ≠ Real.pi := by
    intro h; rw [h, abs_of_pos hpi] at hsarg; linarith
  simp only [one_div, Complex.inv_cpow _ _ hsπ] at hw ⊢
  set u := s ^ (α : ℂ) with hu
  have hu0 : u ≠ 0 := by
    rw [hu, Ne, Complex.cpow_eq_zero_iff]; tauto
  have hlogim : (Complex.log s * α).im = Complex.arg s * α := by
    simp [Complex.mul_im, Complex.log_im]
  have habs : |Complex.arg s * α| < Real.pi := by
    rw [abs_mul, abs_of_pos hα]
    nlinarith [abs_nonneg (Complex.arg s)]
  rw [abs_lt] at habs
  have huarg : Complex.arg u = Complex.arg s * α := by
    rw [hu, Complex.cpow_def_of_ne_zero hs0, ← Complex.log_im,
      Complex.log_exp (by rw [hlogim]; exact habs.1) (by rw [hlogim]; exact habs.2.le), hlogim]
  have hmul : s ^ ((α : ℂ) * γ) = u ^ (γ : ℂ) :=
    Complex.cpow_mul _ (by rw [hlogim]; exact habs.1) (by rw [hlogim]; exact habs.2.le)
  set b := 1 + (c : ℂ) * u⁻¹ with hb
  have hbre : 0 < b.re := by
    have h1 := Complex.abs_re_le_norm ((c : ℂ) * u⁻¹)
    rw [hb, Complex.add_re, Complex.one_re]
    linarith [(abs_le.mp h1).1]
  have hub : u * b = u + c := by rw [hb]; field_simp
  have hb0 : b ≠ 0 := by rintro h; rw [h] at hbre; simp at hbre
  have hsplit : (u + c) ^ (γ : ℂ) = u ^ (γ : ℂ) * b ^ (γ : ℂ) := by
    rw [← hub]
    refine fc2_mul_cpow u b _ hu0 hb0 (fc2_arg_sum u b hu0 ?_ hbre ?_)
    · rw [huarg, abs_lt]; exact habs
    · rw [hub]; simp
  rw [Complex.cpow_neg, Complex.cpow_sub _ _ hs0, hmul, hsplit]
  have h1 : u ^ (γ : ℂ) ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have h2 : b ^ (γ : ℂ) ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have h3 : s ^ (β : ℂ) ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  field_simp

end FractionalCalc

theorem solution (α β γ c : ℝ) (s : ℂ)
    (hα : 0 < α) (hα2 : α ≤ 2) (hβ : 0 < β) (hs : |c| ^ (1 / α) < s.re) :
    laplace (fun t => t ^ (β - 1) * prabhakar α β γ (-c * t ^ α)) s =
      s ^ (α * γ - β : ℂ) / (s ^ (α : ℂ) + c) ^ (γ : ℂ) := by
  have hr0 : 0 < s.re := lt_of_le_of_lt (Real.rpow_nonneg (abs_nonneg c) _) hs
  have hcr : |c| < s.re ^ α := by
    have := Real.rpow_lt_rpow (Real.rpow_nonneg (abs_nonneg c) _) hs hα
    rwa [one_div, Real.rpow_inv_rpow (abs_nonneg c) hα.ne'] at this
  have hs0 : s ≠ 0 := by rintro rfl; simp at hr0
  set q : ℂ := (1 / s) ^ (α : ℂ) with hq
  set ρ : ℝ := |c| * (1 / s.re) ^ α with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by
    have hpos : 0 < (1 / s.re) ^ α := by positivity
    have : s.re ^ α * (1 / s.re) ^ α = 1 := by
      rw [← Real.mul_rpow hr0.le (by positivity), mul_one_div_cancel hr0.ne', Real.one_rpow]
    rw [hρ]; nlinarith
  have hw : ‖(c : ℂ) * q‖ < 1 := by
    refine lt_of_le_of_lt ?_ hρ1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hq, Complex.norm_cpow_real, hρ]
    gcongr
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hr0 (Complex.re_le_norm s)
  set A : ℕ → ℝ := fun k => (∏ j ∈ Finset.range k, (γ + j)) * (-c) ^ k /
    ((k.factorial : ℝ) * Real.Gamma (α * k + β)) with hA
  have hak : ∀ k : ℕ, 0 < α * k + β := fun k => by positivity
  have hAG : ∀ k : ℕ, A k * Real.Gamma (α * k + β) = Ring.choose (-γ) k * c ^ k := by
    intro k
    have hΓ : Real.Gamma (α * k + β) ≠ 0 := (Real.Gamma_pos_of_pos (hak k)).ne'
    have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have h := fc2_choose_neg γ k
    rw [hA]
    field_simp
    rw [neg_pow]
    linear_combination (-(c ^ k)) * h
  set f : ℕ → ℝ → ℂ := fun k t =>
    (A k : ℂ) * (Complex.exp (-s * t) * ((t ^ (α * k + β - 1) : ℝ) : ℂ)) with hf
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      Complex.exp (-s * t) * ((t ^ (β - 1) * prabhakar α β γ (-c * t ^ α) : ℝ) : ℂ) =
        ∑' k, f k t := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have hreal : ∀ k : ℕ, t ^ (β - 1) * ((∏ j ∈ Finset.range k, (γ + j)) * (-c * t ^ α) ^ k /
        ((k.factorial : ℝ) * Real.Gamma (α * k + β))) = A k * t ^ (α * k + β - 1) := by
      intro k
      rw [show α * k + β - 1 = α * k + (β - 1) by ring, Real.rpow_add ht',
        Real.rpow_mul_natCast ht'.le, mul_pow, hA]
      ring
    rw [prabhakar, ← tsum_mul_left, Complex.ofReal_tsum, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [hreal k, hf]
    push_cast
    ring
  have hint : ∀ k, Integrable (f k) (volume.restrict (Ioi 0)) :=
    fun k => (fc2_cint _ (hak k) s hr0).const_mul _
  have hnorm : ∀ k : ℕ, ∫ t in Ioi (0 : ℝ), ‖f k t‖ =
      |A k| * ((1 / s.re) ^ (α * k + β) * Real.Gamma (α * k + β)) := by
    intro k
    simp_rw [hf, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [integral_const_mul, ← fc2_norm_int _ (hak k) s hr0]
    simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hsum : Summable (fun k => ∫ t in Ioi (0 : ℝ), ‖f k t‖) := by
    refine ((fc2_summable_binom (-(γ : ℂ)) ρ hρ0 hρ1).mul_left ((1 / s.re) ^ β)).congr ?_
    intro k
    rw [hnorm k]
    have hΓ := Real.Gamma_pos_of_pos (hak k)
    have e1 : ‖Ring.choose (-(γ : ℂ)) k‖ = |Ring.choose (-γ) k| := by
      rw [← Complex.ofReal_neg, ← Complex.ofReal_choose, Complex.norm_real, Real.norm_eq_abs]
    have e2 : |A k| * Real.Gamma (α * k + β) = |Ring.choose (-γ) k| * |c| ^ k := by
      rw [← abs_of_pos hΓ, ← abs_mul, hAG, abs_mul, abs_pow]
    have e3 : (1 / s.re) ^ (α * k + β) = (1 / s.re) ^ β * ((1 / s.re) ^ α) ^ k := by
      rw [Real.rpow_add (by positivity), Real.rpow_mul_natCast (by positivity)]
      ring
    rw [e1, hρ, e3, mul_pow]
    calc (1 / s.re) ^ β * (|Ring.choose (-γ) k| * (|c| ^ k * ((1 / s.re) ^ α) ^ k))
        = (1 / s.re) ^ β * ((1 / s.re) ^ α) ^ k * (|Ring.choose (-γ) k| * |c| ^ k) := by ring
      _ = _ := by rw [← e2]; ring
  have hval : ∀ k : ℕ, ∫ t in Ioi (0 : ℝ), f k t =
      (1 / s) ^ (β : ℂ) * (Ring.choose (-(γ : ℂ)) k * ((c : ℂ) * q) ^ k) := by
    intro k
    simp_rw [hf]
    rw [integral_const_mul, fc2_lap _ (hak k) s hr0]
    have e1 : (1 / s : ℂ) ^ (((α * k + β : ℝ)) : ℂ) = (1 / s) ^ (β : ℂ) * q ^ k := by
      rw [show (((α * k + β : ℝ)) : ℂ) = (k : ℂ) * α + β by push_cast; ring,
        Complex.cpow_add _ _ (one_div_ne_zero hs0), Complex.cpow_nat_mul]
      ring
    have e2 : (A k : ℂ) * Complex.Gamma ((α * k + β : ℝ)) = Ring.choose (-(γ : ℂ)) k * (c : ℂ) ^ k := by
      rw [Complex.Gamma_ofReal, ← Complex.ofReal_mul, hAG, ← Complex.ofReal_neg,
        ← Complex.ofReal_choose]
      push_cast
      ring
    rw [e1, ← mul_assoc, e2, mul_pow]
    ring
  unfold laplace
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, ← integral_tsum_of_summable_integral_norm hint hsum]
  simp_rw [hval]
  rw [tsum_mul_left, (fc2_hasSum_binom (γ : ℂ) _ hw).tsum_eq]
  exact fc2_alg α β γ c s hα hα2 hr0 hw

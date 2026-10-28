-- Prove2me | solution 1 for FinancialDerivatives.FD06.heatFlow_solves_heat_equation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:26:32.597983+00:00
-- url     : https://prove2.me/submissions/d01755cb-e7f9-40cf-baa8-244562432749

import Mathlib
import Definitions.Def_fd06_gaussianHeatFlow

open FinancialDerivatives.FD06 MeasureTheory ProbabilityTheory

noncomputable def HeatPDE_k (u t : ℝ) : ℝ :=
  Real.exp (-(t ^ 2) / (4 * u)) / Real.sqrt (4 * Real.pi * u)

noncomputable def HeatPDE_kt (u t : ℝ) : ℝ := (t ^ 2 / (4 * u ^ 2) - 1 / (2 * u)) * HeatPDE_k u t

noncomputable def HeatPDE_k1 (u t : ℝ) : ℝ := -(t / (2 * u)) * HeatPDE_k u t

lemma HeatPDE_k_cont (u : ℝ) : Continuous (HeatPDE_k u) := by
  unfold HeatPDE_k; fun_prop

lemma HeatPDE_kt_cont (u : ℝ) : Continuous (HeatPDE_kt u) := by
  have := HeatPDE_k_cont u
  unfold HeatPDE_kt; fun_prop

lemma HeatPDE_k1_cont (u : ℝ) : Continuous (HeatPDE_k1 u) := by
  have := HeatPDE_k_cont u
  unfold HeatPDE_k1; fun_prop

lemma HeatPDE_k_nonneg (u t : ℝ) : 0 ≤ HeatPDE_k u t := by
  unfold HeatPDE_k; positivity

lemma HeatPDE_repr (f : ℝ → ℝ) (hfc : Continuous f) (u y : ℝ) (hu : 0 < u) :
    gaussianHeatFlow f u y = ∫ w, f w * HeatPDE_k u (y - w) := by
  unfold gaussianHeatFlow
  set s := Real.sqrt (2 * u) with hs_def
  have hs2 : s ^ 2 = 2 * u := Real.sq_sqrt (by linarith)
  have hspos : 0 < s := Real.sqrt_pos.2 (by linarith)
  set v : NNReal := NNReal.mk (s ^ 2) (sq_nonneg _) * 1 with hv_def
  have hvv : (v : ℝ) = 2 * u := by simp [v, hs2]
  have hmap : (gaussianReal (0:ℝ) 1).map (fun z => y + s * z) = gaussianReal (s * 0 + y) v := by
    have h1 : (fun z : ℝ => y + s * z) = (y + ·) ∘ (s * ·) := rfl
    rw [h1, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_const_add]
  have hv : v ≠ 0 := by
    intro h
    have := congrArg (fun r : NNReal => (r : ℝ)) h
    simp only [hvv, NNReal.coe_zero] at this
    linarith
  rw [← integral_map (φ := fun z => y + s * z) (by fun_prop) hfc.aestronglyMeasurable, hmap,
    integral_gaussianReal_eq_integral_smul hv]
  congr 1; ext w
  simp only [gaussianPDFReal, smul_eq_mul, HeatPDE_k, hvv, mul_zero, zero_add]
  rw [show 2 * Real.pi * (2 * u) = 4 * Real.pi * u by ring,
    show -(w - y) ^ 2 / (2 * (2 * u)) = -((y - w) ^ 2) / (4 * u) by ring]
  ring

lemma HeatPDE_dom {f : ℝ → ℝ} {M : ℝ} (hfc : Continuous f) (hb : ∀ x, |f x| ≤ M)
    (K K' : ℝ → ℝ → ℝ) (p0 r : ℝ) (hr : 0 < r) (g : ℝ → ℝ)
    (hKc : ∀ p, Continuous (K p)) (hK'c : Continuous (K' p0))
    (hKi : Integrable (K p0))
    (hd : ∀ p ∈ Metric.ball p0 r, ∀ w, HasDerivAt (fun q => K q w) (K' p w) p)
    (hbd : ∀ p ∈ Metric.ball p0 r, ∀ w, |K' p w| ≤ g w) (hg : Integrable g) :
    HasDerivAt (fun p => ∫ w, f w * K p w) (∫ w, f w * K' p0 w) p0 := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hb 0)
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun p w => f w * K p w) (F' := fun p w => f w * K' p w) (x₀ := p0)
    (bound := fun w => M * g w) (Metric.ball_mem_nhds p0 hr)
    (Filter.Eventually.of_forall fun p => (hfc.mul (hKc p)).aestronglyMeasurable)
    (hKi.bdd_mul hfc.aestronglyMeasurable (ae_of_all _ fun w => by
      rw [Real.norm_eq_abs]; exact hb w))
    (hfc.mul hK'c).aestronglyMeasurable
    (ae_of_all _ fun w p hp => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hb w) (hbd p hp w) (abs_nonneg _) hM)
    (hg.const_mul M)
    (ae_of_all _ fun w p hp => (hd p hp w).const_mul (f w))
  exact this.2

lemma HeatPDE_gint (C b c : ℝ) (hb : 0 < b) :
    Integrable (fun w => C * ((1 + (c - w) ^ 2) * Real.exp (-b * (c - w) ^ 2))) := by
  have h0 := integrable_exp_neg_mul_sq hb
  have h2 : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-b * x ^ 2)) := by
    have := integrable_rpow_mul_exp_neg_mul_sq hb (s := 2) (by norm_num)
    simpa [Real.rpow_two] using this
  have h3 : Integrable (fun x : ℝ => (1 + x ^ 2) * Real.exp (-b * x ^ 2)) := by
    refine (h0.add h2).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.add_apply]; ring
  exact (h3.comp_sub_left c).const_mul C

lemma HeatPDE_k_int (u c : ℝ) (hu : 0 < u) : Integrable (fun w => HeatPDE_k u (c - w)) := by
  have : Integrable (fun t : ℝ => (1 / Real.sqrt (4 * Real.pi * u)) *
      Real.exp (-(1 / (4 * u)) * t ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity)).const_mul _
  refine (this.comp_sub_left c).congr (ae_of_all _ fun w => ?_)
  simp only [HeatPDE_k]
  rw [show -(1 / (4 * u)) * (c - w) ^ 2 = -((c - w) ^ 2) / (4 * u) by ring]
  ring

lemma HeatPDE_shift (τ s t : ℝ) (hτ : 0 < τ) (h : |s - t| ≤ 1) :
    HeatPDE_k τ s ≤ (Real.exp (1 / (4 * τ)) / Real.sqrt (4 * Real.pi * τ)) *
      Real.exp (-(1 / (8 * τ)) * t ^ 2) := by
  have hd := abs_le.1 h
  have ht : t ^ 2 ≤ 2 * s ^ 2 + 2 := by nlinarith [sq_nonneg (s - (t - s))]
  have key : -(s ^ 2) / (4 * τ) ≤ 1 / (4 * τ) + -(1 / (8 * τ)) * t ^ 2 := by
    have e : 1 / (4 * τ) + -(1 / (8 * τ)) * t ^ 2 - (-(s ^ 2) / (4 * τ))
        = (2 - t ^ 2 + 2 * s ^ 2) / (8 * τ) := by field_simp; ring
    have : 0 ≤ (2 - t ^ 2 + 2 * s ^ 2) / (8 * τ) := div_nonneg (by linarith) (by positivity)
    linarith
  unfold HeatPDE_k
  calc Real.exp (-(s ^ 2) / (4 * τ)) / Real.sqrt (4 * Real.pi * τ)
      ≤ (Real.exp (1 / (4 * τ)) * Real.exp (-(1 / (8 * τ)) * t ^ 2)) /
          Real.sqrt (4 * Real.pi * τ) :=
        div_le_div_of_nonneg_right (by rw [← Real.exp_add]; exact Real.exp_le_exp.2 key)
          (Real.sqrt_nonneg _)
    _ = _ := by ring

lemma HeatPDE_bound1 (τ u t : ℝ) (hτ : 0 < τ) (hu : u ∈ Metric.ball τ (τ / 2)) :
    |HeatPDE_kt u t| ≤ ((1 / τ ^ 2 + 1 / τ) / Real.sqrt (2 * Real.pi * τ)) *
      ((1 + t ^ 2) * Real.exp (-(1 / (6 * τ)) * t ^ 2)) := by
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hu
  have hu0 : 0 < u := by linarith
  unfold HeatPDE_kt
  rw [abs_mul, abs_of_nonneg (HeatPDE_k_nonneg _ _)]
  have ha : t ^ 2 / (4 * u ^ 2) ≤ t ^ 2 * (1 / τ ^ 2) := by
    rw [← div_eq_mul_one_div]
    exact div_le_div_of_nonneg_left (sq_nonneg t) (by positivity) (by nlinarith)
  have hb : 1 / (2 * u) ≤ 1 / τ := one_div_le_one_div_of_le hτ (by linarith)
  have ha0 : 0 ≤ t ^ 2 / (4 * u ^ 2) := by positivity
  have hb0 : 0 ≤ 1 / (2 * u) := by positivity
  have hA : 0 ≤ 1 / τ ^ 2 := by positivity
  have hB : 0 ≤ 1 / τ := by positivity
  have h1 : |t ^ 2 / (4 * u ^ 2) - 1 / (2 * u)| ≤ (1 / τ ^ 2 + 1 / τ) * (1 + t ^ 2) := by
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg hB (sq_nonneg t), sq_nonneg t]
  have h2 : Real.exp (-(t ^ 2) / (4 * u)) ≤ Real.exp (-(1 / (6 * τ)) * t ^ 2) := by
    apply Real.exp_le_exp.2
    rw [show -(1 / (6 * τ)) * t ^ 2 = -(t ^ 2 / (6 * τ)) by ring, neg_div]
    exact neg_le_neg (div_le_div_of_nonneg_left (sq_nonneg t) (by positivity) (by linarith))
  have h3 : 1 / Real.sqrt (4 * Real.pi * u) ≤ 1 / Real.sqrt (2 * Real.pi * τ) :=
    one_div_le_one_div_of_le (Real.sqrt_pos.2 (by positivity))
      (Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos]))
  unfold HeatPDE_k
  rw [div_eq_mul_one_div (Real.exp _)]
  calc |t ^ 2 / (4 * u ^ 2) - 1 / (2 * u)| *
        (Real.exp (-(t ^ 2) / (4 * u)) * (1 / Real.sqrt (4 * Real.pi * u)))
      ≤ ((1 / τ ^ 2 + 1 / τ) * (1 + t ^ 2)) *
        (Real.exp (-(1 / (6 * τ)) * t ^ 2) * (1 / Real.sqrt (2 * Real.pi * τ))) :=
        mul_le_mul h1 (mul_le_mul h2 h3 (by positivity) (by positivity)) (by positivity)
          (by positivity)
    _ = _ := by ring

lemma HeatPDE_bound2 (τ s t : ℝ) (hτ : 0 < τ) (h : |s - t| ≤ 1) :
    |HeatPDE_k1 τ s| ≤ (1 / τ * (Real.exp (1 / (4 * τ)) / Real.sqrt (4 * Real.pi * τ))) *
      ((1 + t ^ 2) * Real.exp (-(1 / (8 * τ)) * t ^ 2)) := by
  unfold HeatPDE_k1
  rw [abs_mul, abs_neg, abs_div, abs_of_pos (by linarith : (0:ℝ) < 2 * τ),
    abs_of_nonneg (HeatPDE_k_nonneg _ _)]
  have hs : |s| / (2 * τ) ≤ (1 + t ^ 2) * (1 / τ) := by
    rw [div_le_iff₀ (by linarith)]
    have : (1 + t ^ 2) * (1 / τ) * (2 * τ) = 2 * (1 + t ^ 2) := by field_simp
    rw [this]
    nlinarith [abs_sub_abs_le_abs_sub s t, sq_abs t, sq_nonneg (|t| - 1), abs_nonneg t]
  calc |s| / (2 * τ) * HeatPDE_k τ s
      ≤ ((1 + t ^ 2) * (1 / τ)) * ((Real.exp (1 / (4 * τ)) / Real.sqrt (4 * Real.pi * τ)) *
        Real.exp (-(1 / (8 * τ)) * t ^ 2)) :=
        mul_le_mul hs (HeatPDE_shift τ s t hτ h) (HeatPDE_k_nonneg _ _) (by positivity)
    _ = _ := by ring

lemma HeatPDE_bound3 (τ s t : ℝ) (hτ : 0 < τ) (h : |s - t| ≤ 1) :
    |HeatPDE_kt τ s| ≤ ((1 / τ ^ 2 + 1 / τ) *
      (Real.exp (1 / (4 * τ)) / Real.sqrt (4 * Real.pi * τ))) *
      ((1 + t ^ 2) * Real.exp (-(1 / (8 * τ)) * t ^ 2)) := by
  unfold HeatPDE_kt
  rw [abs_mul, abs_of_nonneg (HeatPDE_k_nonneg _ _)]
  have hd := abs_le.1 h
  have hs2 : s ^ 2 ≤ 2 * t ^ 2 + 2 := by nlinarith [sq_nonneg (t - (s - t))]
  have hA : 0 < 1 / τ ^ 2 := by positivity
  have hB : 0 < 1 / τ := by positivity
  have e1 : s ^ 2 / (4 * τ ^ 2) = s ^ 2 * (1 / τ ^ 2) / 4 := by ring
  have e2 : 1 / (2 * τ) = (1 / τ) / 2 := by ring
  have h1 : |s ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)| ≤ (1 + t ^ 2) * (1 / τ ^ 2 + 1 / τ) := by
    rw [e1, e2, abs_le]
    have := mul_le_mul_of_nonneg_right hs2 hA.le
    constructor <;> nlinarith [mul_nonneg hB.le (sq_nonneg t), mul_nonneg hA.le (sq_nonneg s),
      mul_nonneg hA.le (sq_nonneg t)]
  calc |s ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)| * HeatPDE_k τ s
      ≤ ((1 + t ^ 2) * (1 / τ ^ 2 + 1 / τ)) *
        ((Real.exp (1 / (4 * τ)) / Real.sqrt (4 * Real.pi * τ)) *
        Real.exp (-(1 / (8 * τ)) * t ^ 2)) :=
        mul_le_mul h1 (HeatPDE_shift τ s t hτ h) (HeatPDE_k_nonneg _ _) (by positivity)
    _ = _ := by ring

lemma HeatPDE_dt (u t : ℝ) : HasDerivAt (fun t => HeatPDE_k u t) (HeatPDE_k1 u t) t := by
  have h1 := ((hasDerivAt_pow 2 t).neg).div_const (4 * u)
  simp only [Pi.neg_apply, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at h1
  have := (h1.exp).div_const (Real.sqrt (4 * Real.pi * u))
  unfold HeatPDE_k1 HeatPDE_k
  refine this.congr_deriv ?_
  set E := Real.exp (-t ^ 2 / (4 * u))
  set S := Real.sqrt (4 * Real.pi * u)
  ring

lemma HeatPDE_dt1 (u t : ℝ) : HasDerivAt (fun t => HeatPDE_k1 u t) (HeatPDE_kt u t) t := by
  have := (((hasDerivAt_id' t).div_const (2 * u)).neg).mul (HeatPDE_dt u t)
  simp only [Pi.neg_apply] at this
  unfold HeatPDE_kt
  exact this.congr_deriv (by unfold HeatPDE_k1; ring)

lemma HeatPDE_du (u t : ℝ) (hu : 0 < u) :
    HasDerivAt (fun u => HeatPDE_k u t) (HeatPDE_kt u t) u := by
  have h4 : (4 * u) ≠ 0 := by positivity
  have hS : 0 < Real.sqrt (4 * Real.pi * u) := Real.sqrt_pos.2 (by positivity)
  have hS2 : Real.sqrt (4 * Real.pi * u) ^ 2 = 4 * Real.pi * u := Real.sq_sqrt (by positivity)
  have hn := ((hasDerivAt_const u (-(t ^ 2))).div ((hasDerivAt_id' u).const_mul 4) h4).exp
  have hd := ((hasDerivAt_id' u).const_mul (4 * Real.pi)).sqrt (by positivity)
  have := hn.div hd hS.ne'
  unfold HeatPDE_kt HeatPDE_k
  simp only [Pi.div_apply] at this
  refine this.congr_deriv ?_
  have hS2' : Real.sqrt (4 * u * Real.pi) ^ 2 = 4 * u * Real.pi := Real.sq_sqrt (by positivity)
  field_simp
  rw [hS2']
  ring

theorem solution (f : ℝ → ℝ) (M : ℝ) (hf : ContDiff ℝ 2 f) (hb : ∀ x, |f x| ≤ M) (τ x : ℝ) (hτ : 0 < τ) : deriv (fun u => gaussianHeatFlow f u x) τ = deriv (deriv (fun y => gaussianHeatFlow f τ y)) x := by
  have hfc : Continuous f := hf.continuous
  have hT : HasDerivAt (fun u => ∫ w, f w * HeatPDE_k u (x - w))
      (∫ w, f w * HeatPDE_kt τ (x - w)) τ := by
    refine HeatPDE_dom hfc hb (fun u w => HeatPDE_k u (x - w)) (fun u w => HeatPDE_kt u (x - w))
      τ (τ / 2) (by linarith)
      (fun w => ((1 / τ ^ 2 + 1 / τ) / Real.sqrt (2 * Real.pi * τ)) *
        ((1 + (x - w) ^ 2) * Real.exp (-(1 / (6 * τ)) * (x - w) ^ 2)))
      (fun p => (HeatPDE_k_cont p).comp (continuous_const.sub continuous_id))
      ((HeatPDE_kt_cont τ).comp (continuous_const.sub continuous_id))
      (HeatPDE_k_int τ x hτ) ?_ ?_ (HeatPDE_gint _ _ _ (by positivity))
    · intro p hp w
      have : 0 < p := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hp; linarith
      exact HeatPDE_du p (x - w) this
    · intro p hp w
      exact HeatPDE_bound1 τ p (x - w) hτ hp
  have hX1 : ∀ y, HasDerivAt (fun y => ∫ w, f w * HeatPDE_k τ (y - w))
      (∫ w, f w * HeatPDE_k1 τ (y - w)) y := by
    intro y
    refine HeatPDE_dom hfc hb (fun y w => HeatPDE_k τ (y - w)) (fun y w => HeatPDE_k1 τ (y - w))
      y 1 one_pos
      (fun w => (1 / τ * (Real.exp (1 / (4 * τ)) / Real.sqrt (4 * Real.pi * τ))) *
        ((1 + (y - w) ^ 2) * Real.exp (-(1 / (8 * τ)) * (y - w) ^ 2)))
      (fun p => (HeatPDE_k_cont τ).comp (continuous_const.sub continuous_id))
      ((HeatPDE_k1_cont τ).comp (continuous_const.sub continuous_id))
      ?_ ?_ ?_ (HeatPDE_gint _ _ _ (by positivity))
    · exact HeatPDE_k_int τ y hτ
    · intro p _ w
      exact (HeatPDE_dt τ (p - w)).comp_sub_const p w
    · intro p hp w
      rw [Metric.mem_ball, Real.dist_eq] at hp
      exact HeatPDE_bound2 τ (p - w) (y - w) hτ (by rw [show p - w - (y - w) = p - y by ring]; exact hp.le)
  have hX2 : HasDerivAt (fun y => ∫ w, f w * HeatPDE_k1 τ (y - w))
      (∫ w, f w * HeatPDE_kt τ (x - w)) x := by
    refine HeatPDE_dom hfc hb (fun y w => HeatPDE_k1 τ (y - w)) (fun y w => HeatPDE_kt τ (y - w))
      x 1 one_pos
      (fun w => ((1 / τ ^ 2 + 1 / τ) *
        (Real.exp (1 / (4 * τ)) / Real.sqrt (4 * Real.pi * τ))) *
        ((1 + (x - w) ^ 2) * Real.exp (-(1 / (8 * τ)) * (x - w) ^ 2)))
      (fun p => (HeatPDE_k1_cont τ).comp (continuous_const.sub continuous_id))
      ((HeatPDE_kt_cont τ).comp (continuous_const.sub continuous_id))
      ?_ ?_ ?_ (HeatPDE_gint _ _ _ (by positivity))
    · refine (HeatPDE_gint (1 / τ * (Real.exp (1 / (4 * τ)) / Real.sqrt (4 * Real.pi * τ)))
        (1 / (8 * τ)) x (by positivity)).mono'
        ((HeatPDE_k1_cont τ).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
        (ae_of_all _ fun w => ?_)
      rw [Real.norm_eq_abs]
      exact HeatPDE_bound2 τ (x - w) (x - w) hτ (by simp)
    · intro p _ w
      exact (HeatPDE_dt1 τ (p - w)).comp_sub_const p w
    · intro p hp w
      rw [Metric.mem_ball, Real.dist_eq] at hp
      exact HeatPDE_bound3 τ (p - w) (x - w) hτ (by rw [show p - w - (x - w) = p - x by ring]; exact hp.le)
  have e1 : (fun u => gaussianHeatFlow f u x) =ᶠ[nhds τ]
      (fun u => ∫ w, f w * HeatPDE_k u (x - w)) := by
    filter_upwards [lt_mem_nhds hτ] with u hu
    exact HeatPDE_repr f hfc u x hu
  have e2 : (fun y => gaussianHeatFlow f τ y) = (fun y => ∫ w, f w * HeatPDE_k τ (y - w)) :=
    funext fun y => HeatPDE_repr f hfc τ y hτ
  have e3 : deriv (fun y => ∫ w, f w * HeatPDE_k τ (y - w))
      = fun y => ∫ w, f w * HeatPDE_k1 τ (y - w) := funext fun y => (hX1 y).deriv
  rw [e1.deriv_eq, hT.deriv, e2, e3, hX2.deriv]

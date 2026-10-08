-- Prove2me | solution 1 for FreedmanTail.LowerTail.ineq_4_16_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T13:24:49.469041+00:00
-- url     : https://prove2.me/submissions/e8d67f7d-a6b1-477a-9318-f9a81d109498

import Mathlib
import Definitions.Def_FreedmanTail_LowerTail_Exponents
import Definitions.Def_FreedmanTail_LowerTail_Hypotheses
import Definitions.Def_FreedmanTail_LowerTail_ProofNotation
open MeasureTheory


namespace FreedmanTail.LowerTail

lemma e_nonneg (lam : ℝ) : 0 ≤ e lam := by
  unfold e; have := Real.add_one_le_exp lam; linarith

lemma e_le_cubic {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : e t ≤ t ^ 2 / 2 + 2 * t ^ 3 / 9 := by
  have := Real.exp_bound' h0 h1 (n := 3) (by norm_num)
  simp [Finset.sum_range_succ, Nat.factorial] at this
  unfold e; norm_num at this ⊢; nlinarith

lemma chernoff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (a : ℝ)
    (hU : LaplaceUpper P W a) (x : ℝ) (μ : ℝ) (hμ : 0 ≤ μ) :
    P.real {ω | W ω < x} ≤ Real.exp (e μ * x - μ * a) := by
  have hint : Integrable (fun ω => Real.exp (-(e μ * W ω))) P := by
    refine Integrable.of_bound ?_ 1 ?_
    · exact (Real.measurable_exp.comp ((measurable_const.mul hW).neg)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      have := mul_nonneg (e_nonneg μ) (hW0 ω); linarith
  have hM := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := fun ω => Real.exp (-(e μ * W ω)))
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le) hint (Real.exp (-(e μ * x)))
  have hsub : {ω | W ω < x} ⊆ {ω | Real.exp (-(e μ * x)) ≤ Real.exp (-(e μ * W ω))} := by
    intro ω hω; simp only [Set.mem_setOf_eq] at hω ⊢
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hω.le (e_nonneg μ); linarith
  have h1 : P.real {ω | W ω < x} ≤
      P.real {ω | Real.exp (-(e μ * x)) ≤ Real.exp (-(e μ * W ω))} := measureReal_mono hsub
  have h2 := hU μ hμ
  have hε : 0 < Real.exp (-(e μ * x)) := Real.exp_pos _
  have h3 : Real.exp (-(e μ * x)) * P.real {ω | W ω < x} ≤ Real.exp (-(μ * a)) := by
    calc _ ≤ Real.exp (-(e μ * x)) *
          P.real {ω | Real.exp (-(e μ * x)) ≤ Real.exp (-(e μ * W ω))} :=
          mul_le_mul_of_nonneg_left h1 hε.le
      _ ≤ _ := hM
      _ ≤ _ := h2
  rw [show Real.exp (e μ * x - μ * a) = Real.exp (-(μ * a)) / Real.exp (-(e μ * x)) by
    rw [← Real.exp_sub]; ring_nf]
  rw [le_div_iff₀ hε]; linarith [h3]

theorem ineq_4_18_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (a : ℝ) (ha : 0 < a)
    (hU : LaplaceUpper P W a) (x : ℝ) (hx : 0 ≤ x) :
    P.real {ω | W ω < x} < Real.exp (-(a ^ 2 / (2 * (a + x)))) := by
  have hax : 0 < a + x := by linarith
  set t := a / (a + x) with ht
  have ht0 : 0 < t := div_pos ha hax
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hax]; linarith
  have hC := chernoff P W hW hW0 a hU x t ht0.le
  refine lt_of_le_of_lt hC ?_
  apply Real.exp_lt_exp.mpr
  have he := e_le_cubic ht0.le ht1
  have htx : t * (a + x) = a := by rw [ht]; field_simp
  have hgoal : a ^ 2 / (2 * (a + x)) = t * a / 2 := by rw [ht]; field_simp
  rw [hgoal]
  have h1 : e t * x ≤ (t ^ 2 / 2 + 2 * t ^ 3 / 9) * x := mul_le_mul_of_nonneg_right he hx
  have h2 : (t ^ 2 / 2 + 2 * t ^ 3 / 9) * x < t * a / 2 := by
    have : (t ^ 2 / 2 + 2 * t ^ 3 / 9) * x = (t * x) * (t / 2 + 2 * t ^ 2 / 9) := by ring
    rw [this]
    have htx' : t * x = a - t * a := by linarith [htx]
    rw [htx']
    nlinarith [mul_pos (mul_pos ht0 ht0) ha, mul_pos (mul_pos (mul_pos ht0 ht0) ht0) ha]
  linarith


/-! ### Parameter facts -/

lemma log64_gt (δ : ℝ) (hδ : 0 < δ) (hδ3 : δ < 1 / 3) : 6 < Real.log (64 / δ ^ 2) := by
  have h576 : (576 : ℝ) < 64 / δ ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  have he : Real.exp 6 < 576 := by
    have h1 := Real.exp_one_lt_d9
    have h6 : Real.exp 6 = (Real.exp 1) ^ 6 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h6]
    calc (Real.exp 1) ^ 6 < 2.7182818286 ^ 6 := by gcongr
      _ < 576 := by norm_num
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  linarith

lemma params {δ a b : ℝ} (hpar : ParamConditions δ a b) :
    0 < δ ∧ 0 < a ∧ 0 < b ∧ δ < 1 / 3 ∧ 9 * a < δ ^ 2 * b ∧ 6 < Real.log (64 / δ ^ 2) ∧
    16 * Real.log (64 / δ ^ 2) < δ ^ 2 * kStar a b ∧ 9 * kStar a b < δ ^ 2 * a ∧
    864 < kStar a b ∧ a / b < δ ^ 2 / 9 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpar
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hab : 9 * a < δ ^ 2 * b := by
    rw [div_lt_div_iff₀ hδ2 h2] at h5; linarith
  have hL := log64_gt δ h1 h4
  have hk : 16 * Real.log (64 / δ ^ 2) < δ ^ 2 * kStar a b := by
    have := mul_lt_mul_of_pos_right h6 hδ2
    have h' : 16 / δ ^ 2 * Real.log (64 / δ ^ 2) * δ ^ 2 = 16 * Real.log (64 / δ ^ 2) := by
      field_simp
    unfold kStar; linarith
  have hkb : kStar a b * b = a ^ 2 := by unfold kStar; field_simp
  have hk0 : 0 < kStar a b := by unfold kStar; positivity
  have hk9 : 9 * kStar a b < δ ^ 2 * a := by
    apply lt_of_mul_lt_mul_right _ h3.le
    nlinarith
  have hδ2' : δ ^ 2 < 1 / 9 := by nlinarith
  have hk864 : 864 < kStar a b := by
    nlinarith [mul_lt_mul_of_pos_right hδ2' hk0]
  have hr : a / b < δ ^ 2 / 9 := by
    rw [div_lt_div_iff₀ h3 (by norm_num)]; linarith
  exact ⟨h1, h2, h3, h4, hab, hL, hk, hk9, hk864, hr⟩

lemma lam_eq (δ a b : ℝ) : lamStar δ a b = (1 + δ) * (a / b) := by unfold lamStar; ring

lemma phi_eq (lam : ℝ) : phi lam = lam ^ 2 * (3 - lam) / 6 := by unfold phi; ring

lemma phi_pos_of (lam : ℝ) (h0 : 0 < lam) (h3 : lam < 3) : 0 < phi lam := by
  rw [phi_eq]; have : 0 < 3 - lam := by linarith
  positivity

lemma lam_bounds {δ a b : ℝ} (hpar : ParamConditions δ a b) :
    0 < lamStar δ a b ∧ lamStar δ a b < 1 / 50 := by
  obtain ⟨hδ, ha, hb, hδ3, hab, hL, hkL, hk9, hk864, hr⟩ := params hpar
  rw [lam_eq]
  have hr0 : 0 < a / b := by positivity
  constructor
  · positivity
  · have : δ ^ 2 < 1 / 9 := by nlinarith
    nlinarith

lemma phi_lam_pos {δ a b : ℝ} (hpar : ParamConditions δ a b) : 0 < phi (lamStar δ a b) := by
  obtain ⟨h0, h1⟩ := lam_bounds hpar
  exact phi_pos_of _ h0 (by linarith)

lemma phi_mul_b (δ a b : ℝ) (hb : b ≠ 0) :
    phi (lamStar δ a b) * b = kStar a b * ((1 + δ) ^ 2 / 2 - (1 + δ) ^ 3 * (a / b) / 6) := by
  unfold phi lamStar kStar; field_simp

/-! ### Integrals of exponentials -/

lemma integral_exp_Ioc (c : ℝ) (hc : 0 < c) (u v : ℝ) (huv : u ≤ v) :
    ∫ x in Set.Ioc u v, Real.exp (-(c * x)) =
      (Real.exp (-(c * u)) - Real.exp (-(c * v))) / c := by
  rw [← intervalIntegral.integral_of_le huv]
  have hderiv : ∀ x ∈ Set.uIcc u v,
      HasDerivAt (fun x => -Real.exp (-(c * x)) / c) (Real.exp (-(c * x))) x := by
    intro x _
    have h1 : HasDerivAt (fun x => -(c * x)) (-c) x := by
      simpa [neg_mul] using (hasDerivAt_id x).const_mul (-c)
    have h2 := (h1.exp).neg.div_const c
    refine h2.congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; fun_prop)]
  ring

lemma integral_exp_Ioi' (c : ℝ) (hc : 0 < c) (u : ℝ) :
    ∫ x in Set.Ioi u, Real.exp (-(c * x)) = Real.exp (-(c * u)) / c := by
  have := integral_exp_mul_Ioi (a := -c) (by linarith) u
  simp only [neg_mul] at this
  rw [this, neg_div_neg_eq]

lemma exp_integrableOn (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun x => Real.exp (-(c * x))) (Set.Ici 0) := by
  have := integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0
  simp only [neg_mul] at this
  rw [integrableOn_Ici_iff_integrableOn_Ioi]; exact this

/-! ### The tail function -/

lemma tail_mono {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) : Monotone (fun x => P.real {ω | W ω < x}) :=
  fun x y hxy => measureReal_mono (fun ω hω => lt_of_lt_of_le hω hxy)

lemma tail_measurable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) : Measurable (fun x => P.real {ω | W ω < x}) :=
  (tail_mono P W).measurable

lemma tail_le_one {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (x : ℝ) : P.real {ω | W ω < x} ≤ 1 := measureReal_le_one

lemma integrand_integrableOn {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : Ω → ℝ) (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun x => P.real {ω | W ω < x} * Real.exp (-(c * x))) (Set.Ici 0) := by
  refine (exp_integrableOn c hc).mono' ?_ ?_
  · exact ((tail_measurable P W).mul (by fun_prop)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg measureReal_nonneg (Real.exp_pos _).le)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (tail_le_one P W x)

lemma eta_le_of_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (δ a b : ℝ) (I : Set ℝ) (hI : MeasurableSet I) (hI0 : I ⊆ Set.Ici 0) (θ : ℝ)
    (hθ : ∀ x ∈ I, P.real {ω | W ω < x} ≤ θ) (hφ : 0 < phi (lamStar δ a b)) :
    eta P W δ a b I ≤
      phi (lamStar δ a b) * (θ * ∫ x in I, Real.exp (-(phi (lamStar δ a b) * x))) := by
  unfold eta
  apply mul_le_mul_of_nonneg_left _ hφ.le
  rw [← integral_const_mul]
  apply setIntegral_mono_on
  · exact (integrand_integrableOn P W _ hφ).mono_set hI0
  · exact ((exp_integrableOn _ hφ).mono_set hI0).const_mul θ
  · exact hI
  · intro x hx; exact mul_le_mul_of_nonneg_right (hθ x hx) (Real.exp_pos _).le

/-! ### (4.17) -/

theorem ineq_4_17_core (δ a b : ℝ) (hpar : ParamConditions δ a b) :
    Real.exp (-(δ ^ 2 * kStar a b / 8)) < 1 / (8 * kStar a b) := by
  obtain ⟨hδ, ha, hb, hδ3, hab, hL, hkL, hk9, hk864, hr⟩ := params hpar
  set k := kStar a b with hk
  set y := δ ^ 2 * k / 8 with hy
  have hk0 : 0 < k := by linarith
  have hy0 : 0 ≤ y / 2 := by positivity
  have h1 : 64 / δ ^ 2 < Real.exp (y / 2) := by
    rw [← Real.log_lt_iff_lt_exp (by positivity)]; linarith
  have h2 : y ≤ Real.exp (y / 2) := by
    have := Real.quadratic_le_exp_of_nonneg hy0
    nlinarith [sq_nonneg (1 - y / 4)]
  have h3 : Real.exp y = Real.exp (y / 2) * Real.exp (y / 2) := by
    rw [← Real.exp_add]; ring_nf
  have h4 : 8 * k < Real.exp y := by
    have h5 : 8 * k = 64 / δ ^ 2 * y := by rw [hy]; field_simp; ring
    rw [h5, h3]
    have hy1 : 0 < y := by positivity
    have := mul_lt_mul_of_pos_right h1 hy1
    have h6 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (y / 2)).le
    linarith
  rw [Real.exp_neg, one_div]
  exact (inv_lt_inv₀ (Real.exp_pos _) (by positivity)).mpr h4

/-! ### (4.19) -/

theorem ineq_4_19_core
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (δ a b : ℝ)
    (hU : LaplaceUpper P W a) (hL : LaplaceLower P W a) (hpar : ParamConditions δ a b) :
    ∀ x : ℝ, 0 ≤ x → x ≤ NStar δ * a →
      P.real {ω | W ω < x} < (1 / 8 - 1 / 50) * Real.exp (-((1 + δ) * kStar a b)) := by
  intro x hx0 hx1
  obtain ⟨hδ, ha, hb, hδ3, hab, hL, hkL, hk9, hk864, hr⟩ := params hpar
  have h18 := ineq_4_18_core P W hW hW0 a ha hU x hx0
  refine lt_of_lt_of_le h18 ?_
  rw [show (1 / 8 - 1 / 50 : ℝ) * Real.exp (-((1 + δ) * kStar a b))
      = Real.exp (Real.log (1 / 8 - 1 / 50) + -((1 + δ) * kStar a b)) by
    rw [Real.exp_add, Real.exp_log (by norm_num)]]
  apply Real.exp_le_exp.mpr
  have hlog : -9 ≤ Real.log (1 / 8 - 1 / 50) := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (1 / 8 - 1 / 50)⁻¹ by norm_num)
    rw [Real.log_inv] at this; norm_num at this ⊢; linarith
  have hN : NStar δ * a = 2 * a / δ ^ 2 := by unfold NStar; ring
  rw [hN] at hx1
  have hx1' : δ ^ 2 * x ≤ 2 * a := by
    rw [le_div_iff₀ (by positivity)] at hx1; linarith
  set k := kStar a b with hk
  have hk0 : 0 < k := by linarith
  have hδ2 : δ ^ 2 < 1 / 9 := by nlinarith
  suffices h : (1 + δ) * k + 9 ≤ a ^ 2 / (2 * (a + x)) by linarith
  rw [le_div_iff₀ (by positivity)]
  have hpos : 0 ≤ (1 + δ) * k + 9 := by positivity
  apply le_of_mul_le_mul_left _ (show 0 < δ ^ 2 by positivity)
  calc δ ^ 2 * (((1 + δ) * k + 9) * (2 * (a + x)))
      = ((1 + δ) * k + 9) * (2 * (δ ^ 2 * a + δ ^ 2 * x)) := by ring
    _ ≤ ((1 + δ) * k + 9) * (2 * (δ ^ 2 * a + 2 * a)) := by gcongr
    _ = ((1 + δ) * k + 9) * 2 * a * (δ ^ 2 + 2) := by ring
    _ ≤ ((1 + δ) * k + 9) * 2 * a * (19 / 9) := by gcongr; linarith
    _ ≤ (4 / 3 * k + 9) * 2 * a * (19 / 9) := by gcongr; linarith
    _ ≤ 9 * k * a := by nlinarith [mul_pos ha (by linarith : (0 : ℝ) < k - 864)]
    _ ≤ δ ^ 2 * a ^ 2 := by nlinarith [mul_lt_mul_of_pos_right hk9 ha]

/-! ### (4.16:1) -/

theorem ineq_4_16_1_core
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (δ a b : ℝ)
    (hU : LaplaceUpper P W a) (hL : LaplaceLower P W a) (hpar : ParamConditions δ a b) :
    eta P W δ a b (I1 δ a) < (1 / 8 - 1 / 50) * Real.exp (-((1 + δ) * kStar a b)) := by
  obtain ⟨hδ, ha, hb, hδ3, hab, hL', hkL, hk9, hk864, hr⟩ := params hpar
  have hφ := phi_lam_pos hpar
  set θ := (1 / 8 - 1 / 50) * Real.exp (-((1 + δ) * kStar a b)) with hθ
  have hθ0 : 0 < θ := by positivity
  have h19 := ineq_4_19_core P W hW hW0 δ a b hU hL hpar
  have hNa : 0 ≤ NStar δ * a := by unfold NStar; positivity
  have hb1 := eta_le_of_bound P W δ a b (I1 δ a) measurableSet_Icc Set.Icc_subset_Ici_self θ
    (fun x hx => (h19 x hx.1 hx.2).le) hφ
  refine lt_of_le_of_lt hb1 ?_
  unfold I1
  rw [integral_Icc_eq_integral_Ioc, integral_exp_Ioc _ hφ _ _ hNa, mul_zero, neg_zero,
    Real.exp_zero]
  set φ := phi (lamStar δ a b) with hφdef
  have hE : 0 < Real.exp (-(φ * (NStar δ * a))) := Real.exp_pos _
  rw [show φ * (θ * ((1 - Real.exp (-(φ * (NStar δ * a)))) / φ))
      = θ * (1 - Real.exp (-(φ * (NStar δ * a)))) by field_simp]
  nlinarith

/-! ### (4.16:4) -/

theorem ineq_4_16_4_core
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (δ a b : ℝ)
    (hU : LaplaceUpper P W a) (hL : LaplaceLower P W a) (hpar : ParamConditions δ a b) :
    eta P W δ a b (I4 b) < 1 / 8 * Real.exp (-((1 + δ) * kStar a b)) := by
  obtain ⟨hδ, ha, hb, hδ3, hab, hL', hkL, hk9, hk864, hr⟩ := params hpar
  have hφ := phi_lam_pos hpar
  have hb1 := eta_le_of_bound P W δ a b (I4 b) measurableSet_Ioi
    (by intro x hx; simp only [I4, Set.mem_Ioi, Set.mem_Ici] at hx ⊢; linarith) 1
    (fun x _ => tail_le_one P W x) hφ
  refine lt_of_le_of_lt hb1 ?_
  unfold I4
  rw [integral_exp_Ioi' _ hφ, one_mul, mul_div_cancel₀ _ hφ.ne']
  rw [show (1 / 8 : ℝ) * Real.exp (-((1 + δ) * kStar a b))
      = Real.exp (Real.log (1 / 8) + -((1 + δ) * kStar a b)) by
    rw [Real.exp_add, Real.exp_log (by norm_num)]]
  apply Real.exp_lt_exp.mpr
  have hlog : -7 ≤ Real.log (1 / 8) := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (1 / 8)⁻¹ by norm_num)
    rw [Real.log_inv] at this; norm_num at this ⊢; linarith
  have hφb := phi_mul_b δ a b hb.ne'
  rw [show phi (lamStar δ a b) * (2 * b) = 2 * (phi (lamStar δ a b) * b) by ring, hφb]
  set k := kStar a b with hk
  set r := a / b with hrdef
  have hk0 : 0 < k := by linarith
  have hr0 : 0 < r := by positivity
  have hkδ : 288 < k * δ := by
    have h1 : δ * (k * δ) < 1 / 3 * (k * δ) := mul_lt_mul_of_pos_right hδ3 (mul_pos hk0 hδ)
    nlinarith
  have h16 : (1 + δ) ^ 2 < 16 / 9 := by nlinarith
  have hs1 : (1 + δ) ^ 2 * r < 16 / 9 * (δ ^ 2 / 9) :=
    mul_lt_mul'' h16 hr (by positivity) hr0.le
  have hδδ : δ ^ 2 < δ / 3 := by nlinarith
  have hs : (1 + δ) ^ 2 * r / 3 < δ / 2 := by nlinarith
  have hA : 0 < k * (1 + δ) * (δ / 2 - (1 + δ) ^ 2 * r / 3) :=
    mul_pos (mul_pos hk0 (by linarith)) (by linarith)
  nlinarith [mul_nonneg hk0.le (sq_nonneg δ)]

end FreedmanTail.LowerTail

open FreedmanTail.LowerTail


theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (δ a b : ℝ)
    (hU : LaplaceUpper P W a) (hL : LaplaceLower P W a) (hpar : ParamConditions δ a b) :
    eta P W δ a b (I1 δ a) < (1 / 8 - 1 / 50) * Real.exp (-((1 + δ) * kStar a b)) := by
  exact ineq_4_16_1_core P W hW hW0 δ a b hU hL hpar

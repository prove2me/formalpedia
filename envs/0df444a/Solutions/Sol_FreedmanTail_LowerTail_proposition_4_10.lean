-- Prove2me | solution 1 for FreedmanTail.LowerTail.proposition_4_10
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T13:53:13.249861+00:00
-- url     : https://prove2.me/submissions/3b2718f9-cf84-422d-bd4b-ff403028412f

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

lemma delta_pows {δ : ℝ} (hδ : 0 < δ) (hδ3 : δ < 1 / 3) :
    δ ^ 2 ≤ 1 / 9 ∧ δ ^ 3 ≤ 1 / 27 ∧ δ ^ 4 ≤ 1 / 81 ∧ δ ^ 5 ≤ 1 / 243 ∧ δ ^ 6 ≤ 1 / 729 := by
  have h2 := pow_le_pow_left₀ hδ.le hδ3.le 2
  have h3 := pow_le_pow_left₀ hδ.le hδ3.le 3
  have h4 := pow_le_pow_left₀ hδ.le hδ3.le 4
  have h5 := pow_le_pow_left₀ hδ.le hδ3.le 5
  have h6 := pow_le_pow_left₀ hδ.le hδ3.le 6
  norm_num at h2 h3 h4 h5 h6
  exact ⟨h2, h3, h4, h5, h6⟩

lemma polyI2_F (δ r D Φ : ℝ) (hD : D = r + 1 - 2 * δ)
    (hΦ : Φ = (1 + δ) ^ 2 / 2 - (1 + δ) ^ 3 * r / 6)
    (hδ : 0 < δ) (hδ3 : δ < 1 / 3) (hr0 : 0 ≤ r) (hr : r ≤ δ ^ 2 / 9) :
    (1 + δ + δ ^ 2 / 8) * (2 * D) ≤ 1 + 2 * D * Φ * (1 - 2 * δ) := by
  subst hD hΦ
  obtain ⟨h2, h3, h4, h5, h6⟩ := delta_pows hδ hδ3
  have hr2 : r ^ 2 ≤ δ ^ 2 / 729 := by nlinarith
  have hF1 : -3 ≤ -(16 * δ ^ 5 + 32 * δ ^ 4 + 28 * δ ^ 3 + 19 * δ ^ 2 + 20 * δ + 16) / 12 := by
    nlinarith
  have hF2 : -1 ≤ (δ + 1) ^ 3 * (2 * δ - 1) / 3 := by nlinarith
  have hA : -3 * r ≤ r * (-(16 * δ ^ 5 + 32 * δ ^ 4 + 28 * δ ^ 3 + 19 * δ ^ 2 + 20 * δ + 16) / 12) := by
    nlinarith
  have hB : -(r ^ 2) ≤ r ^ 2 * ((δ + 1) ^ 3 * (2 * δ - 1) / 3) := by nlinarith [sq_nonneg r]
  have hid : 1 + 2 * (r + 1 - 2 * δ) * ((1 + δ) ^ 2 / 2 - (1 + δ) ^ 3 * r / 6) * (1 - 2 * δ)
      - (1 + δ + δ ^ 2 / 8) * (2 * (r + 1 - 2 * δ))
      = (4 * δ ^ 4 + 9 * δ ^ 3 / 2 + 3 * δ ^ 2 / 4)
        + r * (-(16 * δ ^ 5 + 32 * δ ^ 4 + 28 * δ ^ 3 + 19 * δ ^ 2 + 20 * δ + 16) / 12)
        + r ^ 2 * ((δ + 1) ^ 3 * (2 * δ - 1) / 3) := by ring
  nlinarith [pow_pos hδ 3, pow_pos hδ 4]

lemma polyI2_slope (δ r D Φ : ℝ) (hD : D = r + 1 - 2 * δ)
    (hΦ : Φ = (1 + δ) ^ 2 / 2 - (1 + δ) ^ 3 * r / 6)
    (hδ : 0 < δ) (hδ3 : δ < 1 / 3) (hr0 : 0 ≤ r) (hr : r ≤ δ ^ 2 / 9) :
    Φ * (2 * D ^ 2) ≤ 1 := by
  subst hD hΦ
  obtain ⟨h2, h3, h4, h5, h6⟩ := delta_pows hδ hδ3
  have hr2 : r ^ 2 ≤ δ ^ 2 / 729 := by nlinarith
  have hr3 : r ^ 3 ≤ δ ^ 2 / 729 := by nlinarith [sq_nonneg r]
  have hc1 : -2 ≤ 4 * δ ^ 5 / 3 + 8 * δ ^ 4 / 3 + 13 * δ ^ 3 / 3 + 13 * δ ^ 2 / 3 - δ / 3 - 5 / 3 := by
    nlinarith [pow_pos hδ 2, pow_pos hδ 3, pow_pos hδ 4, pow_pos hδ 5]
  have hc2 : -2 ≤ -4 * δ ^ 4 / 3 - 10 * δ ^ 3 / 3 - 3 * δ ^ 2 - 4 * δ / 3 - 1 / 3 := by nlinarith
  have hc3 : 0 ≤ δ ^ 3 / 3 + δ ^ 2 + δ + 1 / 3 := by positivity
  have hA : -2 * r ≤ r * (4 * δ ^ 5 / 3 + 8 * δ ^ 4 / 3 + 13 * δ ^ 3 / 3 + 13 * δ ^ 2 / 3 - δ / 3 - 5 / 3) := by
    nlinarith
  have hB : -2 * r ^ 2 ≤ r ^ 2 * (-4 * δ ^ 4 / 3 - 10 * δ ^ 3 / 3 - 3 * δ ^ 2 - 4 * δ / 3 - 1 / 3) := by
    nlinarith [sq_nonneg r]
  have hC : 0 ≤ r ^ 3 * (δ ^ 3 / 3 + δ ^ 2 + δ + 1 / 3) := by positivity
  have hid : 1 - ((1 + δ) ^ 2 / 2 - (1 + δ) ^ 3 * r / 6) * (2 * (r + 1 - 2 * δ) ^ 2)
      = (-4 * δ ^ 4 - 4 * δ ^ 3 + 3 * δ ^ 2 + 2 * δ)
        + r * (4 * δ ^ 5 / 3 + 8 * δ ^ 4 / 3 + 13 * δ ^ 3 / 3 + 13 * δ ^ 2 / 3 - δ / 3 - 5 / 3)
        + r ^ 2 * (-4 * δ ^ 4 / 3 - 10 * δ ^ 3 / 3 - 3 * δ ^ 2 - 4 * δ / 3 - 1 / 3)
        + r ^ 3 * (δ ^ 3 / 3 + δ ^ 2 + δ + 1 / 3) := by ring
  nlinarith [pow_pos hδ 2, pow_pos hδ 3, pow_pos hδ 4]

lemma polyI3_F (δ r D Φ : ℝ) (hD : D = 1 + r)
    (hΦ : Φ = (1 + δ) ^ 2 / 2 - (1 + δ) ^ 3 * r / 6)
    (hδ : 0 < δ) (hδ3 : δ < 1 / 3) (hr0 : 0 ≤ r) (hr : r ≤ δ ^ 2 / 9) :
    (1 + δ + δ ^ 2 / 8) * (2 * D) ≤ 1 + 2 * D * Φ := by
  subst hD hΦ
  obtain ⟨h2, h3, h4, h5, h6⟩ := delta_pows hδ hδ3
  have hr2 : r ^ 2 ≤ δ ^ 2 / 729 := by nlinarith
  have hF1 : -2 ≤ -(4 * δ ^ 3 + 3 * δ ^ 2 + 12 * δ + 16) / 12 := by nlinarith
  have hF2 : -1 ≤ -(δ + 1) ^ 3 / 3 := by nlinarith
  have hA : -2 * r ≤ r * (-(4 * δ ^ 3 + 3 * δ ^ 2 + 12 * δ + 16) / 12) := by nlinarith
  have hB : -(r ^ 2) ≤ r ^ 2 * (-(δ + 1) ^ 3 / 3) := by nlinarith [sq_nonneg r]
  have hid : 1 + 2 * (1 + r) * ((1 + δ) ^ 2 / 2 - (1 + δ) ^ 3 * r / 6)
      - (1 + δ + δ ^ 2 / 8) * (2 * (1 + r))
      = 3 * δ ^ 2 / 4 + r * (-(4 * δ ^ 3 + 3 * δ ^ 2 + 12 * δ + 16) / 12)
        + r ^ 2 * (-(δ + 1) ^ 3 / 3) := by ring
  nlinarith

lemma polyI3_slope (δ r D Φ : ℝ) (hD : D = 1 + r)
    (hΦ : Φ = (1 + δ) ^ 2 / 2 - (1 + δ) ^ 3 * r / 6)
    (hδ : 0 < δ) (hδ3 : δ < 1 / 3) (hr0 : 0 ≤ r) (hr : r ≤ δ ^ 2 / 9) :
    1 ≤ Φ * (2 * D ^ 2) := by
  subst hD hΦ
  obtain ⟨h2, h3, h4, h5, h6⟩ := delta_pows hδ hδ3
  have hr3 : r ^ 3 ≤ δ ^ 2 / 729 := by nlinarith [sq_nonneg r]
  have hc1 : 0 ≤ -δ ^ 3 / 3 + δ ^ 2 + 3 * δ + 5 / 3 := by nlinarith
  have hc2 : 0 ≤ -2 * δ ^ 3 / 3 - δ ^ 2 + 1 / 3 := by nlinarith
  have hc3 : -1 ≤ -δ ^ 3 / 3 - δ ^ 2 - δ - 1 / 3 := by nlinarith
  have hA : 0 ≤ r * (-δ ^ 3 / 3 + δ ^ 2 + 3 * δ + 5 / 3) := mul_nonneg hr0 hc1
  have hB : 0 ≤ r ^ 2 * (-2 * δ ^ 3 / 3 - δ ^ 2 + 1 / 3) := mul_nonneg (sq_nonneg r) hc2
  have hC : -(r ^ 3) ≤ r ^ 3 * (-δ ^ 3 / 3 - δ ^ 2 - δ - 1 / 3) := by
    nlinarith [pow_nonneg hr0 3]
  have hid : ((1 + δ) ^ 2 / 2 - (1 + δ) ^ 3 * r / 6) * (2 * (1 + r) ^ 2) - 1
      = (δ ^ 2 + 2 * δ) + r * (-δ ^ 3 / 3 + δ ^ 2 + 3 * δ + 5 / 3)
        + r ^ 2 * (-2 * δ ^ 3 / 3 - δ ^ 2 + 1 / 3)
        + r ^ 3 * (-δ ^ 3 / 3 - δ ^ 2 - δ - 1 / 3) := by ring
  nlinarith [pow_pos hδ 2]

lemma psi_lower_I2 (δ r s : ℝ) (hδ : 0 < δ) (hδ3 : δ < 1 / 3) (hr0 : 0 ≤ r) (hr : r ≤ δ ^ 2 / 9)
    (hs0 : 0 < s) (hs : s ≤ 1 - 2 * δ) :
    1 + δ + δ ^ 2 / 8 ≤ 1 / (2 * (r + s)) + ((1 + δ) ^ 2 / 2 - (1 + δ) ^ 3 * r / 6) * s := by
  have hD0 : 0 < r + 1 - 2 * δ := by linarith
  have hrs : 0 < r + s := by linarith
  have hslope := polyI2_slope δ r _ _ rfl rfl hδ hδ3 hr0 hr
  have hF := polyI2_F δ r _ _ rfl rfl hδ hδ3 hr0 hr
  generalize hΦ : (1 + δ) ^ 2 / 2 - (1 + δ) ^ 3 * r / 6 = Φ at hslope hF ⊢
  generalize hD : r + 1 - 2 * δ = D at hslope hF hD0 ⊢
  have hT : 1 / D - (r + s) / (2 * D ^ 2) ≤ 1 / (2 * (r + s)) := by
    have h1 : 1 / (2 * (r + s)) - (1 / D - (r + s) / (2 * D ^ 2))
        = (s - (D - r)) ^ 2 / (2 * (r + s) * D ^ 2) := by
      field_simp; ring
    have h2 : 0 ≤ (s - (D - r)) ^ 2 / (2 * (r + s) * D ^ 2) := by positivity
    linarith
  have hslope' : Φ ≤ 1 / (2 * D ^ 2) := by
    rw [le_div_iff₀ (by positivity)]; exact hslope
  have hcomb : 1 / (2 * D) + Φ * (1 - 2 * δ) ≤ 1 / D - (r + s) / (2 * D ^ 2) + Φ * s := by
    have h1 : 1 / D - (r + s) / (2 * D ^ 2) = 1 / (2 * D) + ((1 - 2 * δ) - s) / (2 * D ^ 2) := by
      field_simp; rw [← hD]; ring
    rw [h1]
    have h3 : ((1 - 2 * δ) - s) * Φ ≤ ((1 - 2 * δ) - s) * (1 / (2 * D ^ 2)) :=
      mul_le_mul_of_nonneg_left hslope' (by linarith)
    have h4 : ((1 - 2 * δ) - s) / (2 * D ^ 2) = ((1 - 2 * δ) - s) * (1 / (2 * D ^ 2)) := by ring
    linarith
  have hfin : 1 + δ + δ ^ 2 / 8 ≤ 1 / (2 * D) + Φ * (1 - 2 * δ) := by
    rw [show 1 / (2 * D) + Φ * (1 - 2 * δ) = (1 + 2 * D * Φ * (1 - 2 * δ)) / (2 * D) by
      field_simp]
    rw [le_div_iff₀ (by positivity)]
    exact hF
  linarith

lemma psi_lower_I3 (δ r s : ℝ) (hδ : 0 < δ) (hδ3 : δ < 1 / 3) (hr0 : 0 ≤ r) (hr : r ≤ δ ^ 2 / 9)
    (hs : 1 ≤ s) :
    1 + δ + δ ^ 2 / 8 ≤ 1 / (2 * (r + s)) + ((1 + δ) ^ 2 / 2 - (1 + δ) ^ 3 * r / 6) * s := by
  have hD0 : 0 < 1 + r := by linarith
  have hrs : 0 < r + s := by linarith
  have hslope := polyI3_slope δ r _ _ rfl rfl hδ hδ3 hr0 hr
  have hF := polyI3_F δ r _ _ rfl rfl hδ hδ3 hr0 hr
  generalize hΦ : (1 + δ) ^ 2 / 2 - (1 + δ) ^ 3 * r / 6 = Φ at hslope hF ⊢
  generalize hD : 1 + r = D at hslope hF hD0 ⊢
  have hT : 1 / D - (r + s) / (2 * D ^ 2) ≤ 1 / (2 * (r + s)) := by
    have h1 : 1 / (2 * (r + s)) - (1 / D - (r + s) / (2 * D ^ 2))
        = (s - (D - r)) ^ 2 / (2 * (r + s) * D ^ 2) := by
      field_simp; ring
    have h2 : 0 ≤ (s - (D - r)) ^ 2 / (2 * (r + s) * D ^ 2) := by positivity
    linarith
  have hslope' : 1 / (2 * D ^ 2) ≤ Φ := by
    rw [div_le_iff₀ (by positivity)]; exact hslope
  have hcomb : 1 / (2 * D) + Φ ≤ 1 / D - (r + s) / (2 * D ^ 2) + Φ * s := by
    have h1 : 1 / D - (r + s) / (2 * D ^ 2) = 1 / (2 * D) + (1 - s) / (2 * D ^ 2) := by
      field_simp; rw [← hD]; ring
    rw [h1]
    have h3 : (s - 1) * (1 / (2 * D ^ 2)) ≤ (s - 1) * Φ :=
      mul_le_mul_of_nonneg_left hslope' (by linarith)
    have h4 : (1 - s) / (2 * D ^ 2) = -((s - 1) * (1 / (2 * D ^ 2))) := by ring
    linarith
  have hfin : 1 + δ + δ ^ 2 / 8 ≤ 1 / (2 * D) + Φ := by
    rw [show 1 / (2 * D) + Φ = (1 + 2 * D * Φ) / (2 * D) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    exact hF
  linarith


/-! ### Laplace transform as a layer-cake integral -/

lemma exp_neg_le_quad {u : ℝ} (hu : 0 ≤ u) : Real.exp (-u) ≤ 1 - u + u ^ 2 / 2 := by
  have h1 := Real.quadratic_le_exp_of_nonneg hu
  have h3 : 0 < 1 - u + u ^ 2 / 2 := by nlinarith [sq_nonneg (1 - u)]
  have h4 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  by_contra h
  push_neg at h
  have h5 := mul_lt_mul_of_pos_right h (Real.exp_pos u)
  nlinarith [mul_le_mul_of_nonneg_left h1 h3.le, sq_nonneg (u ^ 2)]

lemma f_nonneg (u : ℝ) : 0 ≤ f u := by
  unfold f; have := Real.add_one_le_exp (-u); linarith

lemma exp_neg_lt_quad {u : ℝ} (hu : 0 < u) : Real.exp (-u) < 1 - u + u ^ 2 / 2 := by
  have h1 := Real.quadratic_le_exp_of_nonneg hu.le
  have h3 : 0 < 1 - u + u ^ 2 / 2 := by nlinarith [sq_nonneg (1 - u)]
  have h4 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  by_contra h
  push_neg at h
  have h5 := mul_le_mul_of_nonneg_right h (Real.exp_pos u).le
  nlinarith [mul_le_mul_of_nonneg_left h1 h3.le, pow_pos hu 4]

lemma f_gt_phi {lam : ℝ} (h : 0 < lam) : phi lam < f lam := by
  have hmono : StrictMonoOn
      (fun x : ℝ => Real.exp (-x) - 1 + x - x ^ 2 / 2 + x ^ 3 / 6) (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact Continuous.continuousOn (by fun_prop)
    · intro x hx
      rw [interior_Ici] at hx
      have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-x)) x := by
        simpa using (hasDerivAt_neg x).exp
      have h3 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
        have := (hasDerivAt_pow 2 x).div_const 2
        refine this.congr_deriv ?_
        norm_num <;> ring
      have h4 : HasDerivAt (fun y : ℝ => y ^ 3 / 6) (x ^ 2 / 2) x := by
        have := (hasDerivAt_pow 3 x).div_const 6
        refine this.congr_deriv ?_
        norm_num <;> ring
      have hd : HasDerivAt (fun x : ℝ => Real.exp (-x) - 1 + x - x ^ 2 / 2 + x ^ 3 / 6)
          (-Real.exp (-x) + 1 - x + x ^ 2 / 2) x :=
        (((h1.sub_const 1).add (hasDerivAt_id x)).sub h3).add h4
      rw [hd.deriv]
      have := exp_neg_lt_quad hx
      linarith
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h.le) h
  simp at this
  unfold phi f; linarith

lemma exp_neg_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (c : ℝ) (hc : 0 ≤ c) :
    Integrable (fun ω => Real.exp (-(c * W ω))) P := by
  refine Integrable.of_bound ?_ 1 ?_
  · exact (Real.measurable_exp.comp ((measurable_const.mul hW).neg)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    have := mul_nonneg hc (hW0 ω); linarith

lemma laplace_layer {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (c : ℝ) (hc : 0 < c) :
    ∫ ω, Real.exp (-(c * W ω)) ∂P
      = c * ∫ x in Set.Ici 0, P.real {ω | W ω < x} * Real.exp (-(c * x)) := by
  have hg_cont : Continuous (fun t : ℝ => c * Real.exp (-(c * t))) := by fun_prop
  have hg_int : ∀ t > 0, IntervalIntegrable (fun t : ℝ => c * Real.exp (-(c * t))) volume 0 t :=
    fun t _ => hg_cont.intervalIntegrable 0 t
  have hg_nn : ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)), 0 ≤ c * Real.exp (-(c * t)) :=
    Filter.Eventually.of_forall fun t => by positivity
  have key := lintegral_comp_eq_lintegral_meas_le_mul P (f := W)
    (Filter.Eventually.of_forall hW0) hW.aemeasurable hg_int hg_nn
  have hG : ∀ w : ℝ, ∫ t in (0 : ℝ)..w, c * Real.exp (-(c * t)) = 1 - Real.exp (-(c * w)) := by
    intro w
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) w,
        HasDerivAt (fun x => -Real.exp (-(c * x))) (c * Real.exp (-(c * x))) x := by
      intro x _
      have h1 : HasDerivAt (fun x => -(c * x)) (-c) x := by
        simpa [neg_mul] using (hasDerivAt_id x).const_mul (-c)
      exact (h1.exp).neg.congr_deriv (by ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hg_cont.intervalIntegrable _ _)]
    simp only [mul_zero, neg_zero, Real.exp_zero]; ring
  simp_rw [hG] at key
  have hexp_int := exp_neg_integrable P W hW hW0 c hc.le
  have hexp_le1 : ∀ ω, Real.exp (-(c * W ω)) ≤ 1 := fun ω => by
    apply Real.exp_le_one_iff.mpr; have := mul_nonneg hc.le (hW0 ω); linarith
  have hint1 : Integrable (fun ω => 1 - Real.exp (-(c * W ω))) P :=
    (integrable_const 1).sub hexp_int
  have hL : ∫⁻ ω, ENNReal.ofReal (1 - Real.exp (-(c * W ω))) ∂P
      = ENNReal.ofReal (1 - ∫ ω, Real.exp (-(c * W ω)) ∂P) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint1
      (Filter.Eventually.of_forall fun ω => by simp only [Pi.zero_apply]; linarith [hexp_le1 ω])]
    congr 1
    rw [integral_sub (integrable_const 1) hexp_int]
    simp
  have hanti : Antitone (fun t => P.real {a | t ≤ W a}) :=
    fun x y hxy => measureReal_mono (fun ω hω => le_trans hxy hω)
  have hgi : IntegrableOn (fun t : ℝ => c * Real.exp (-(c * t))) (Set.Ioi 0) := by
    have := integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0
    simp only [neg_mul] at this
    exact this.const_mul c
  have hint2 : IntegrableOn (fun t => P.real {a | t ≤ W a} * (c * Real.exp (-(c * t))))
      (Set.Ioi 0) := by
    refine hgi.mono' ?_ ?_
    · exact (hanti.measurable.mul hg_cont.measurable).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun t => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg measureReal_nonneg (by positivity))]
      exact mul_le_of_le_one_left (by positivity) measureReal_le_one
  have hR : ∫⁻ t in Set.Ioi 0, P {a | t ≤ W a} * ENNReal.ofReal (c * Real.exp (-(c * t)))
      = ENNReal.ofReal (∫ t in Set.Ioi 0, P.real {a | t ≤ W a} * (c * Real.exp (-(c * t)))) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint2
      (Filter.Eventually.of_forall fun t => mul_nonneg measureReal_nonneg (by positivity))]
    apply lintegral_congr
    intro t
    rw [ENNReal.ofReal_mul measureReal_nonneg, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hL, hR] at key
  have hnn1 : 0 ≤ 1 - ∫ ω, Real.exp (-(c * W ω)) ∂P := by
    have : ∫ ω, Real.exp (-(c * W ω)) ∂P ≤ ∫ _ω, (1 : ℝ) ∂P :=
      integral_mono hexp_int (integrable_const 1) hexp_le1
    simp at this; linarith
  have hnn2 : 0 ≤ ∫ t in Set.Ioi 0, P.real {a | t ≤ W a} * (c * Real.exp (-(c * t))) :=
    integral_nonneg fun t => mul_nonneg measureReal_nonneg (by positivity)
  have key' := (ENNReal.ofReal_eq_ofReal_iff hnn1 hnn2).mp key
  have hcompl : ∀ t, P.real {a | t ≤ W a} = 1 - P.real {a | W a < t} := by
    intro t
    have : {a | t ≤ W a} = {a | W a < t}ᶜ := by ext a; simp
    rw [this, measureReal_compl (measurableSet_lt hW measurable_const), probReal_univ]
  simp_rw [hcompl] at key'
  have hint3 : IntegrableOn (fun t => P.real {a | W a < t} * Real.exp (-(c * t))) (Set.Ioi 0) :=
    (integrand_integrableOn P W c hc).mono_set Set.Ioi_subset_Ici_self
  have hsplit : ∫ t in Set.Ioi 0, (1 - P.real {a | W a < t}) * (c * Real.exp (-(c * t)))
      = (∫ t in Set.Ioi 0, c * Real.exp (-(c * t)))
        - c * ∫ t in Set.Ioi 0, P.real {a | W a < t} * Real.exp (-(c * t)) := by
    rw [← integral_const_mul, ← integral_sub hgi (hint3.const_mul c)]
    congr 1; ext t; ring
  have hg1 : ∫ t in Set.Ioi 0, c * Real.exp (-(c * t)) = 1 := by
    rw [integral_const_mul, integral_exp_Ioi' c hc 0, mul_zero, neg_zero, Real.exp_zero]
    field_simp
  rw [hsplit, hg1] at key'
  rw [integral_Ici_eq_integral_Ioi]
  linarith

/-! ### (4.15) -/

theorem ineq_4_15_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (δ a b : ℝ)
    (hL : LaplaceLower P W a) (hpar : ParamConditions δ a b) :
    Real.exp (-(lamStar δ a b * (a + 1))) <
      phi (lamStar δ a b) *
        ∫ x in Set.Ici (0 : ℝ), P.real {ω | W ω < x} *
          Real.exp (-(phi (lamStar δ a b) * x)) := by
  have hφ := phi_lam_pos hpar
  obtain ⟨hl0, hl1⟩ := lam_bounds hpar
  obtain ⟨hδ, ha, hb, hδ3, hab, hL6, hkL, hk9, hk864, hr⟩ := params hpar
  rw [← laplace_layer P W hW hW0 _ hφ]
  have hfφ := f_gt_phi hl0
  have hLL := hL (lamStar δ a b) hl0.le
  have hint_f := exp_neg_integrable P W hW hW0 _ (f_nonneg (lamStar δ a b))
  have hint_φ := exp_neg_integrable P W hW hW0 _ hφ.le
  have hpt : ∀ ω, Real.exp (-(f (lamStar δ a b) * W ω))
      ≤ Real.exp (-(phi (lamStar δ a b) * W ω)) := fun ω => by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right hfφ.le (hW0 ω); linarith
  have hdiff_nn : 0 ≤ fun ω => Real.exp (-(phi (lamStar δ a b) * W ω))
      - Real.exp (-(f (lamStar δ a b) * W ω)) := fun ω => by
    simp only [Pi.zero_apply, sub_nonneg]; exact hpt ω
  have hdiff_int : Integrable (fun ω => Real.exp (-(phi (lamStar δ a b) * W ω))
      - Real.exp (-(f (lamStar δ a b) * W ω))) P := hint_φ.sub hint_f
  by_cases hzero : ∫ ω, (Real.exp (-(phi (lamStar δ a b) * W ω))
      - Real.exp (-(f (lamStar δ a b) * W ω))) ∂P = 0
  · have hae := (integral_eq_zero_iff_of_nonneg hdiff_nn hdiff_int).mp hzero
    have hW_ae : ∀ᵐ ω ∂P, Real.exp (-(phi (lamStar δ a b) * W ω)) = 1 := by
      filter_upwards [hae] with ω hω
      simp only [Pi.zero_apply] at hω
      have h1 : Real.exp (-(phi (lamStar δ a b) * W ω))
          = Real.exp (-(f (lamStar δ a b) * W ω)) := by linarith
      have h2 := Real.exp_injective h1
      have h3 : W ω = 0 := by
        by_contra hne
        have hpos : 0 < W ω := lt_of_le_of_ne (hW0 ω) (Ne.symm hne)
        have := mul_pos (sub_pos.mpr hfφ) hpos
        nlinarith
      rw [h3]; simp
    have : ∫ ω, Real.exp (-(phi (lamStar δ a b) * W ω)) ∂P = 1 := by
      rw [integral_congr_ae hW_ae]; simp
    rw [this]
    apply Real.exp_lt_one_iff.mpr
    nlinarith
  · have hpos : 0 < ∫ ω, (Real.exp (-(phi (lamStar δ a b) * W ω))
        - Real.exp (-(f (lamStar δ a b) * W ω))) ∂P :=
      lt_of_le_of_ne (integral_nonneg hdiff_nn) (Ne.symm hzero)
    rw [integral_sub hint_φ hint_f] at hpos
    linarith

/-! ### `P{W < b} > 0` -/

lemma prob_lt_b_pos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (δ a b : ℝ)
    (hL : LaplaceLower P W a) (hpar : ParamConditions δ a b) :
    0 < P.real {ω | W ω < b} := by
  obtain ⟨hδ, ha, hb, hδ3, hab, hL6, hkL, hk9, hk864, hr⟩ := params hpar
  by_contra h
  push_neg at h
  have h0 : P.real {ω | W ω < b} = 0 := le_antisymm h measureReal_nonneg
  have hae : ∀ᵐ ω ∂P, b ≤ W ω := by
    rw [measureReal_eq_zero_iff] at h0
    rw [ae_iff]; simpa using h0
  have hLL := hL 1 zero_le_one
  have hf1 : f 1 = Real.exp (-1) := by unfold f; ring
  have hint := exp_neg_integrable P W hW hW0 (f 1) (f_nonneg 1)
  have hle : ∫ ω, Real.exp (-(f 1 * W ω)) ∂P ≤ Real.exp (-(f 1 * b)) := by
    have := integral_mono_ae hint (integrable_const (Real.exp (-(f 1 * b))))
      (hae.mono fun ω hω => by
        apply Real.exp_le_exp.mpr
        have := mul_le_mul_of_nonneg_left hω (f_nonneg 1); linarith)
    simpa using this
  have hδ2 : δ ^ 2 < 1 / 9 := by nlinarith
  have hb81 : 81 * a < b := by nlinarith [mul_lt_mul_of_pos_right hδ2 hb]
  have ha1 : 1 < a := by nlinarith [mul_lt_mul_of_pos_right hδ2 ha]
  have hexp : 1 / 3 < Real.exp (-1) := by
    have := Real.exp_one_lt_d9
    rw [Real.exp_neg, lt_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
    linarith
  have hfinal := hLL.trans hle
  rw [Real.exp_le_exp, hf1] at hfinal
  nlinarith

/-! ### (4.16:5) -/

theorem ineq_4_16_5_core
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (δ a b : ℝ)
    (hU : LaplaceUpper P W a) (hL : LaplaceLower P W a) (hpar : ParamConditions δ a b) :
    eta P W δ a b (I5 δ b) <
      P.real {ω | W ω < b} * Real.exp ((-(1 / 2) + 2 * δ ^ 2) * kStar a b) := by
  obtain ⟨hδ, ha, hb, hδ3, hab, hL6, hkL, hk9, hk864, hr⟩ := params hpar
  have hφ := phi_lam_pos hpar
  have hpb := prob_lt_b_pos P W hW hW0 δ a b hL hpar
  have hu0 : 0 ≤ (1 - 2 * δ) * b := by nlinarith
  have huv : (1 - 2 * δ) * b ≤ b := by nlinarith
  have hb1 := eta_le_of_bound P W δ a b (I5 δ b) measurableSet_Ioc
    (by intro x hx; simp only [I5, Set.mem_Ioc, Set.mem_Ici] at hx ⊢; linarith)
    (P.real {ω | W ω < b}) (fun x hx => tail_mono P W hx.2) hφ
  refine lt_of_le_of_lt hb1 ?_
  unfold I5
  rw [integral_exp_Ioc _ hφ _ _ huv]
  rw [show phi (lamStar δ a b) * (P.real {ω | W ω < b} *
      ((Real.exp (-(phi (lamStar δ a b) * ((1 - 2 * δ) * b)))
        - Real.exp (-(phi (lamStar δ a b) * b))) / phi (lamStar δ a b)))
      = P.real {ω | W ω < b} * (Real.exp (-(phi (lamStar δ a b) * ((1 - 2 * δ) * b)))
        - Real.exp (-(phi (lamStar δ a b) * b))) by field_simp]
  apply mul_lt_mul_of_pos_left _ hpb
  have he2 : 0 < Real.exp (-(phi (lamStar δ a b) * b)) := Real.exp_pos _
  have he1 : Real.exp (-(phi (lamStar δ a b) * ((1 - 2 * δ) * b)))
      ≤ Real.exp ((-(1 / 2) + 2 * δ ^ 2) * kStar a b) := by
    apply Real.exp_le_exp.mpr
    have hφb := phi_mul_b δ a b hb.ne'
    rw [show phi (lamStar δ a b) * ((1 - 2 * δ) * b) = (1 - 2 * δ) * (phi (lamStar δ a b) * b)
      by ring, hφb]
    have hk0 : 0 < kStar a b := by linarith
    have hr0 : 0 ≤ a / b := by positivity
    have h27 : (1 + δ) ^ 3 ≤ 64 / 27 := by nlinarith
    have h1 : (1 + δ) ^ 3 * (a / b) ≤ 64 / 27 * (δ ^ 2 / 9) :=
      mul_le_mul h27 hr.le hr0 (by norm_num)
    have h2 : 0 ≤ 1 - 2 * δ := by linarith
    have hmain : 1 / 2 - 2 * δ ^ 2
        ≤ (1 - 2 * δ) * ((1 + δ) ^ 2 / 2 - (1 + δ) ^ 3 * (a / b) / 6) := by
      nlinarith [mul_le_mul_of_nonneg_left h1 h2,
        mul_nonneg (sq_nonneg δ) (by linarith : (0 : ℝ) ≤ 1 / 2 - δ)]
    nlinarith [mul_le_mul_of_nonneg_left hmain hk0.le]
  linarith

/-! ### pointwise bounds on an interval -/

lemma eta_le_of_pointwise {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (δ a b : ℝ) (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (M : ℝ)
    (hM : ∀ x ∈ Set.Ioc u v,
      P.real {ω | W ω < x} * Real.exp (-(phi (lamStar δ a b) * x)) ≤ M)
    (hφ : 0 < phi (lamStar δ a b)) :
    eta P W δ a b (Set.Ioc u v) ≤ phi (lamStar δ a b) * (M * (v - u)) := by
  unfold eta
  apply mul_le_mul_of_nonneg_left _ hφ.le
  calc ∫ x in Set.Ioc u v, P.real {ω | W ω < x} * Real.exp (-(phi (lamStar δ a b) * x))
      ≤ ∫ _x in Set.Ioc u v, M := by
        apply setIntegral_mono_on
        · exact (integrand_integrableOn P W _ hφ).mono_set
            (fun x hx => Set.mem_Ici.mpr (le_trans hu hx.1.le))
        · exact integrableOn_const measure_Ioc_lt_top.ne
        · exact measurableSet_Ioc
        · exact hM
    _ = M * (v - u) := by
        rw [setIntegral_const, Real.volume_real_Ioc_of_le huv, smul_eq_mul, mul_comm]

/-! ### (4.16:2) -/

theorem ineq_4_16_2_core
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (δ a b : ℝ)
    (hU : LaplaceUpper P W a) (hL : LaplaceLower P W a) (hpar : ParamConditions δ a b) :
    eta P W δ a b (I2 δ a b) < 1 / 8 * Real.exp (-((1 + δ) * kStar a b)) := by
  obtain ⟨hδ, ha, hb, hδ3, hab, hL6, hkL, hk9, hk864, hr⟩ := params hpar
  have hφ := phi_lam_pos hpar
  have hk0 : 0 < kStar a b := by linarith
  have hr0 : 0 ≤ a / b := by positivity
  have hb' : b ≠ 0 := hb.ne'
  have hφb := phi_mul_b δ a b hb'
  have hNa : NStar δ * a = 2 * a / δ ^ 2 := by unfold NStar; ring
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hu0 : 0 ≤ NStar δ * a := by rw [hNa]; positivity
  have huv : NStar δ * a ≤ (1 - 2 * δ) * b := by
    rw [hNa, div_le_iff₀ hδ2]
    nlinarith [mul_pos hδ2 hb]
  have hE : Real.exp (-((1 + δ) * kStar a b + δ ^ 2 * kStar a b / 8))
      = Real.exp (-((1 + δ) * kStar a b)) * Real.exp (-(δ ^ 2 * kStar a b / 8)) := by
    rw [← Real.exp_add]; ring_nf
  have hM : ∀ x ∈ Set.Ioc (NStar δ * a) ((1 - 2 * δ) * b),
      P.real {ω | W ω < x} * Real.exp (-(phi (lamStar δ a b) * x))
        ≤ Real.exp (-((1 + δ) * kStar a b + δ ^ 2 * kStar a b / 8)) := by
    intro x hx
    have hx0 : 0 < x := lt_of_le_of_lt hu0 hx.1
    have h18 := (ineq_4_18_core P W hW hW0 a ha hU x hx0.le).le
    calc P.real {ω | W ω < x} * Real.exp (-(phi (lamStar δ a b) * x))
        ≤ Real.exp (-(a ^ 2 / (2 * (a + x)))) * Real.exp (-(phi (lamStar δ a b) * x)) :=
          mul_le_mul_of_nonneg_right h18 (Real.exp_pos _).le
      _ = Real.exp (-(a ^ 2 / (2 * (a + x)) + phi (lamStar δ a b) * x)) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          have hax : a + x ≠ 0 := by positivity
          have h1 : a ^ 2 / (2 * (a + x)) = kStar a b * (1 / (2 * (a / b + x / b))) := by
            unfold kStar; field_simp
          have h2 : phi (lamStar δ a b) * x
              = kStar a b * (((1 + δ) ^ 2 / 2 - (1 + δ) ^ 3 * (a / b) / 6) * (x / b)) := by
            rw [show phi (lamStar δ a b) * x = (phi (lamStar δ a b) * b) * (x / b) by
              field_simp, hφb]; ring
          have hs0 : 0 < x / b := by positivity
          have hs1 : x / b ≤ 1 - 2 * δ := by rw [div_le_iff₀ hb]; exact hx.2
          have hψ := psi_lower_I2 δ (a / b) (x / b) hδ hδ3 hr0 hr.le hs0 hs1
          rw [h1, h2]
          nlinarith [mul_le_mul_of_nonneg_left hψ hk0.le]
  have hb1 := eta_le_of_pointwise P W δ a b _ _ hu0 huv _ hM hφ
  unfold I2
  refine lt_of_le_of_lt hb1 ?_
  have h17 := ineq_4_17_core δ a b hpar
  have hw : (1 - 2 * δ) * b - NStar δ * a ≤ b := by nlinarith
  have hφb_le : phi (lamStar δ a b) * b ≤ kStar a b := by
    rw [hφb]
    have : (1 + δ) ^ 2 / 2 - (1 + δ) ^ 3 * (a / b) / 6 ≤ 1 := by
      nlinarith [mul_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + δ) 3) hr0]
    nlinarith [mul_le_mul_of_nonneg_left this hk0.le]
  rw [hE]
  have hE1 : 0 < Real.exp (-((1 + δ) * kStar a b)) := Real.exp_pos _
  have hE2 : 0 < Real.exp (-(δ ^ 2 * kStar a b / 8)) := Real.exp_pos _
  calc phi (lamStar δ a b) * (Real.exp (-((1 + δ) * kStar a b))
        * Real.exp (-(δ ^ 2 * kStar a b / 8)) * ((1 - 2 * δ) * b - NStar δ * a))
      ≤ phi (lamStar δ a b) * (Real.exp (-((1 + δ) * kStar a b))
        * Real.exp (-(δ ^ 2 * kStar a b / 8)) * b) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw (by positivity)) hφ.le
    _ = (phi (lamStar δ a b) * b) * Real.exp (-(δ ^ 2 * kStar a b / 8))
        * Real.exp (-((1 + δ) * kStar a b)) := by ring
    _ ≤ kStar a b * Real.exp (-(δ ^ 2 * kStar a b / 8))
        * Real.exp (-((1 + δ) * kStar a b)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hφb_le hE2.le) hE1.le
    _ < kStar a b * (1 / (8 * kStar a b)) * Real.exp (-((1 + δ) * kStar a b)) :=
        mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left h17 hk0) hE1
    _ = 1 / 8 * Real.exp (-((1 + δ) * kStar a b)) := by field_simp

/-! ### (4.16:3) -/

theorem ineq_4_16_3_core
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (δ a b : ℝ)
    (hU : LaplaceUpper P W a) (hL : LaplaceLower P W a) (hpar : ParamConditions δ a b) :
    eta P W δ a b (I3 b) < 1 / 8 * Real.exp (-((1 + δ) * kStar a b)) := by
  obtain ⟨hδ, ha, hb, hδ3, hab, hL6, hkL, hk9, hk864, hr⟩ := params hpar
  have hφ := phi_lam_pos hpar
  have hk0 : 0 < kStar a b := by linarith
  have hr0 : 0 ≤ a / b := by positivity
  have hb' : b ≠ 0 := hb.ne'
  have hφb := phi_mul_b δ a b hb'
  have hu0 : 0 ≤ b := hb.le
  have huv : b ≤ 2 * b := by linarith
  have hE : Real.exp (-((1 + δ) * kStar a b + δ ^ 2 * kStar a b / 8))
      = Real.exp (-((1 + δ) * kStar a b)) * Real.exp (-(δ ^ 2 * kStar a b / 8)) := by
    rw [← Real.exp_add]; ring_nf
  have hM : ∀ x ∈ Set.Ioc b (2 * b),
      P.real {ω | W ω < x} * Real.exp (-(phi (lamStar δ a b) * x))
        ≤ Real.exp (-((1 + δ) * kStar a b + δ ^ 2 * kStar a b / 8)) := by
    intro x hx
    have hx0 : 0 < x := lt_of_le_of_lt hu0 hx.1
    have h18 := (ineq_4_18_core P W hW hW0 a ha hU x hx0.le).le
    calc P.real {ω | W ω < x} * Real.exp (-(phi (lamStar δ a b) * x))
        ≤ Real.exp (-(a ^ 2 / (2 * (a + x)))) * Real.exp (-(phi (lamStar δ a b) * x)) :=
          mul_le_mul_of_nonneg_right h18 (Real.exp_pos _).le
      _ = Real.exp (-(a ^ 2 / (2 * (a + x)) + phi (lamStar δ a b) * x)) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          have hax : a + x ≠ 0 := by positivity
          have h1 : a ^ 2 / (2 * (a + x)) = kStar a b * (1 / (2 * (a / b + x / b))) := by
            unfold kStar; field_simp
          have h2 : phi (lamStar δ a b) * x
              = kStar a b * (((1 + δ) ^ 2 / 2 - (1 + δ) ^ 3 * (a / b) / 6) * (x / b)) := by
            rw [show phi (lamStar δ a b) * x = (phi (lamStar δ a b) * b) * (x / b) by
              field_simp, hφb]; ring
          have hs1 : 1 ≤ x / b := by rw [le_div_iff₀ hb]; linarith [hx.1]
          have hψ := psi_lower_I3 δ (a / b) (x / b) hδ hδ3 hr0 hr.le hs1
          rw [h1, h2]
          nlinarith [mul_le_mul_of_nonneg_left hψ hk0.le]
  have hb1 := eta_le_of_pointwise P W δ a b _ _ hu0 huv _ hM hφ
  unfold I3
  refine lt_of_le_of_lt hb1 ?_
  have h17 := ineq_4_17_core δ a b hpar
  have hw : 2 * b - b ≤ b := by linarith
  have hφb_le : phi (lamStar δ a b) * b ≤ kStar a b := by
    rw [hφb]
    have : (1 + δ) ^ 2 / 2 - (1 + δ) ^ 3 * (a / b) / 6 ≤ 1 := by
      nlinarith [mul_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + δ) 3) hr0]
    nlinarith [mul_le_mul_of_nonneg_left this hk0.le]
  rw [hE]
  have hE1 : 0 < Real.exp (-((1 + δ) * kStar a b)) := Real.exp_pos _
  have hE2 : 0 < Real.exp (-(δ ^ 2 * kStar a b / 8)) := Real.exp_pos _
  calc phi (lamStar δ a b) * (Real.exp (-((1 + δ) * kStar a b))
        * Real.exp (-(δ ^ 2 * kStar a b / 8)) * (2 * b - b))
      ≤ phi (lamStar δ a b) * (Real.exp (-((1 + δ) * kStar a b))
        * Real.exp (-(δ ^ 2 * kStar a b / 8)) * b) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw (by positivity)) hφ.le
    _ = (phi (lamStar δ a b) * b) * Real.exp (-(δ ^ 2 * kStar a b / 8))
        * Real.exp (-((1 + δ) * kStar a b)) := by ring
    _ ≤ kStar a b * Real.exp (-(δ ^ 2 * kStar a b / 8))
        * Real.exp (-((1 + δ) * kStar a b)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hφb_le hE2.le) hE1.le
    _ < kStar a b * (1 / (8 * kStar a b)) * Real.exp (-((1 + δ) * kStar a b)) :=
        mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left h17 hk0) hE1
    _ = 1 / 8 * Real.exp (-((1 + δ) * kStar a b)) := by field_simp

/-! ### splitting the integral -/

lemma integral_split (g : ℝ → ℝ) (hg : IntegrableOn g (Set.Ici 0)) (u₁ u₂ u₃ u₄ : ℝ)
    (h0 : 0 ≤ u₁) (h1 : u₁ ≤ u₂) (h2 : u₂ ≤ u₃) (h3 : u₃ ≤ u₄) :
    ∫ x in Set.Ici 0, g x = (∫ x in Set.Icc 0 u₁, g x) + (∫ x in Set.Ioc u₁ u₂, g x)
      + (∫ x in Set.Ioc u₂ u₃, g x) + (∫ x in Set.Ioc u₃ u₄, g x) + (∫ x in Set.Ioi u₄, g x) := by
  have h02 : 0 ≤ u₂ := h0.trans h1
  have h03 : 0 ≤ u₃ := h02.trans h2
  have h04 : 0 ≤ u₄ := h03.trans h3
  have e1 : Set.Icc 0 u₁ ∪ Set.Ioc u₁ u₂ = Set.Icc 0 u₂ := Set.Icc_union_Ioc_eq_Icc h0 h1
  have e2 : Set.Icc 0 u₂ ∪ Set.Ioc u₂ u₃ = Set.Icc 0 u₃ := Set.Icc_union_Ioc_eq_Icc h02 h2
  have e3 : Set.Icc 0 u₃ ∪ Set.Ioc u₃ u₄ = Set.Icc 0 u₄ := Set.Icc_union_Ioc_eq_Icc h03 h3
  have e4 : Set.Icc 0 u₄ ∪ Set.Ioi u₄ = Set.Ici 0 := Set.Icc_union_Ioi_eq_Ici h04
  have hsub : ∀ s : Set ℝ, s ⊆ Set.Ici 0 → IntegrableOn g s := fun s hs => hg.mono_set hs
  have d1 : Disjoint (Set.Icc 0 u₁) (Set.Ioc u₁ u₂) := Set.disjoint_left.mpr
    (fun x hx hx' => by simp only [Set.mem_Icc, Set.mem_Ioc] at hx hx'; linarith)
  have d2 : Disjoint (Set.Icc 0 u₂) (Set.Ioc u₂ u₃) := Set.disjoint_left.mpr
    (fun x hx hx' => by simp only [Set.mem_Icc, Set.mem_Ioc] at hx hx'; linarith)
  have d3 : Disjoint (Set.Icc 0 u₃) (Set.Ioc u₃ u₄) := Set.disjoint_left.mpr
    (fun x hx hx' => by simp only [Set.mem_Icc, Set.mem_Ioc] at hx hx'; linarith)
  have d4 : Disjoint (Set.Icc 0 u₄) (Set.Ioi u₄) := Set.disjoint_left.mpr
    (fun x hx hx' => by simp only [Set.mem_Icc, Set.mem_Ioi] at hx hx'; linarith)
  rw [← e4, setIntegral_union d4 measurableSet_Ioi (hsub _ Set.Icc_subset_Ici_self)
    (hsub _ (fun x hx => Set.mem_Ici.mpr (le_trans h04 (le_of_lt hx))))]
  rw [← e3, setIntegral_union d3 measurableSet_Ioc (hsub _ Set.Icc_subset_Ici_self)
    (hsub _ (fun x hx => Set.mem_Ici.mpr (le_trans h03 hx.1.le)))]
  rw [← e2, setIntegral_union d2 measurableSet_Ioc (hsub _ Set.Icc_subset_Ici_self)
    (hsub _ (fun x hx => Set.mem_Ici.mpr (le_trans h02 hx.1.le)))]
  rw [← e1, setIntegral_union d1 measurableSet_Ioc (hsub _ Set.Icc_subset_Ici_self)
    (hsub _ (fun x hx => Set.mem_Ici.mpr (le_trans h0 hx.1.le)))]

/-! ### Proposition (4.10) -/

theorem proposition_4_10_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (δ a b : ℝ)
    (hU : LaplaceUpper P W a) (hL : LaplaceLower P W a) (hpar : ParamConditions δ a b) :
    1 / 2 * Real.exp (-((1 / 2 + 2 * δ) * a ^ 2 / b)) < P.real {ω | W ω < b} := by
  obtain ⟨hδ, ha, hb, hδ3, hab, hL6, hkL, hk9, hk864, hr⟩ := params hpar
  have hφ := phi_lam_pos hpar
  obtain ⟨hl0, hl1⟩ := lam_bounds hpar
  have hk0 : 0 < kStar a b := by linarith
  have h15 := ineq_4_15_core P W hW hW0 δ a b hL hpar
  have h1 := ineq_4_16_1_core P W hW hW0 δ a b hU hL hpar
  have h2 := ineq_4_16_2_core P W hW hW0 δ a b hU hL hpar
  have h3 := ineq_4_16_3_core P W hW hW0 δ a b hU hL hpar
  have h4 := ineq_4_16_4_core P W hW hW0 δ a b hU hL hpar
  have h5 := ineq_4_16_5_core P W hW hW0 δ a b hU hL hpar
  have hNa : NStar δ * a = 2 * a / δ ^ 2 := by unfold NStar; ring
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hu0 : 0 ≤ NStar δ * a := by rw [hNa]; positivity
  have huv : NStar δ * a ≤ (1 - 2 * δ) * b := by
    rw [hNa, div_le_iff₀ hδ2]
    nlinarith [mul_pos hδ2 hb]
  have hsplit : ∫ x in Set.Ici 0, P.real {ω | W ω < x} * Real.exp (-(phi (lamStar δ a b) * x))
      = (∫ x in Set.Icc 0 (NStar δ * a), P.real {ω | W ω < x} * Real.exp (-(phi (lamStar δ a b) * x)))
      + (∫ x in Set.Ioc (NStar δ * a) ((1 - 2 * δ) * b),
          P.real {ω | W ω < x} * Real.exp (-(phi (lamStar δ a b) * x)))
      + (∫ x in Set.Ioc ((1 - 2 * δ) * b) b,
          P.real {ω | W ω < x} * Real.exp (-(phi (lamStar δ a b) * x)))
      + (∫ x in Set.Ioc b (2 * b), P.real {ω | W ω < x} * Real.exp (-(phi (lamStar δ a b) * x)))
      + (∫ x in Set.Ioi (2 * b), P.real {ω | W ω < x} * Real.exp (-(phi (lamStar δ a b) * x))) :=
    integral_split _ (integrand_integrableOn P W _ hφ) _ _ _ _ hu0 huv (by nlinarith) (by linarith)
  rw [hsplit] at h15
  simp only [eta, I1, I2, I3, I4, I5] at h1 h2 h3 h4 h5
  have hdist : ∀ A B C D E : ℝ, phi (lamStar δ a b) * (A + B + C + D + E)
      = phi (lamStar δ a b) * A + phi (lamStar δ a b) * B + phi (lamStar δ a b) * C
        + phi (lamStar δ a b) * D + phi (lamStar δ a b) * E := fun A B C D E => by ring
  rw [hdist] at h15
  have hlam_a : lamStar δ a b * a = (1 + δ) * kStar a b := by
    unfold lamStar kStar; field_simp
  have hexplam : Real.exp (-(lamStar δ a b * (a + 1)))
      = Real.exp (-((1 + δ) * kStar a b)) * Real.exp (-lamStar δ a b) := by
    rw [← Real.exp_add, ← hlam_a]; ring_nf
  have hE : 0 < Real.exp (-((1 + δ) * kStar a b)) := Real.exp_pos _
  have hexpneg : 1 - lamStar δ a b ≤ Real.exp (-lamStar δ a b) := by
    have := Real.add_one_le_exp (-lamStar δ a b); linarith
  have hlow : Real.exp (-((1 + δ) * kStar a b)) * (1 - 1 / 50)
      < Real.exp (-(lamStar δ a b * (a + 1))) := by
    rw [hexplam]
    have := mul_le_mul_of_nonneg_left hexpneg hE.le
    have := mul_lt_mul_of_pos_left hl1 hE
    nlinarith
  have hη5 : Real.exp (-((1 + δ) * kStar a b)) / 2
      < phi (lamStar δ a b) * ∫ x in Set.Ioc ((1 - 2 * δ) * b) b,
          P.real {ω | W ω < x} * Real.exp (-(phi (lamStar δ a b) * x)) := by
    linarith
  have hX : 0 < Real.exp ((-(1 / 2) + 2 * δ ^ 2) * kStar a b) := Real.exp_pos _
  have hY : Real.exp (-((1 + δ) * kStar a b))
      = Real.exp (-((1 / 2 + δ + 2 * δ ^ 2) * kStar a b))
        * Real.exp ((-(1 / 2) + 2 * δ ^ 2) * kStar a b) := by
    rw [← Real.exp_add]; congr 1; ring
  have hp : Real.exp (-((1 / 2 + δ + 2 * δ ^ 2) * kStar a b)) / 2 < P.real {ω | W ω < b} := by
    have h6 : Real.exp (-((1 / 2 + δ + 2 * δ ^ 2) * kStar a b)) / 2
        * Real.exp ((-(1 / 2) + 2 * δ ^ 2) * kStar a b)
        < P.real {ω | W ω < b} * Real.exp ((-(1 / 2) + 2 * δ ^ 2) * kStar a b) := by
      rw [hY] at hη5
      linarith
    exact lt_of_mul_lt_mul_right h6 hX.le
  have hmono : Real.exp (-((1 / 2 + 2 * δ) * a ^ 2 / b))
      ≤ Real.exp (-((1 / 2 + δ + 2 * δ ^ 2) * kStar a b)) := by
    apply Real.exp_le_exp.mpr
    unfold kStar
    have : (1 / 2 + δ + 2 * δ ^ 2) * (a ^ 2 / b) ≤ (1 / 2 + 2 * δ) * a ^ 2 / b := by
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith
    linarith
  linarith

end FreedmanTail.LowerTail

open FreedmanTail.LowerTail


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (δ a b : ℝ)
    (hU : LaplaceUpper P W a) (hL : LaplaceLower P W a) (hpar : ParamConditions δ a b) :
    1 / 2 * Real.exp (-((1 / 2 + 2 * δ) * a ^ 2 / b)) < P.real {ω | W ω < b} := by
  exact proposition_4_10_core P W hW hW0 δ a b hU hL hpar

-- Prove2me | solution 1 for CachonCoord.Newsvendor.p25_supplier_foc
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T06:33:11.248702+00:00
-- url     : https://prove2.me/submissions/192188ef-e5f9-496b-84b6-76432baa11e9

import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts

open MeasureTheory ProbabilityTheory


namespace CachonCoord.Newsvendor

lemma nv_cdf_cont (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D] :
    Continuous (cdf D) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hs : (cdf D).measure {x} = 0 := by rw [measure_cdf]; exact measure_singleton x
  rw [StieltjesFunction.measure_singleton, ENNReal.ofReal_eq_zero] at hs
  have hle : Function.leftLim (cdf D) x ≤ cdf D x := (monotone_cdf D).leftLim_le le_rfl
  have heq : Function.leftLim (cdf D) x = cdf D x := le_antisymm hle (by linarith)
  have hl : ContinuousWithinAt (cdf D) (Set.Iio x) x :=
    ((monotone_cdf D).continuousWithinAt_Iio_iff_leftLim_eq).2 heq
  have hr : ContinuousWithinAt (cdf D) (Set.Ici x) x := (cdf D).right_continuous x
  exact continuousAt_iff_continuous_left_right.2 ⟨continuousWithinAt_Iio_iff_Iic.1 hl, hr⟩

lemma nv_cdf_nonpos (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (hD0 : D (Set.Iio 0) = 0) (x : ℝ) (hx : x ≤ 0) : cdf D x = 0 := by
  have h1 : D (Set.Iic x) = 0 := by
    apply le_antisymm _ (zero_le)
    calc D (Set.Iic x) ≤ D (Set.Iio 0 ∪ {0}) := measure_mono (by
            intro y hy; simp only [Set.mem_Iic] at hy
            rcases lt_or_eq_of_le (hy.trans hx) with h | h
            · exact Or.inl h
            · exact Or.inr h)
      _ ≤ D (Set.Iio 0) + D {0} := measure_union_le _ _
      _ = 0 := by rw [hD0, measure_singleton]; simp
  rw [cdf_eq_real, measureReal_def, h1]; simp

lemma nv_ae_nonneg (D : Measure ℝ) (hD0 : D (Set.Iio 0) = 0) : ∀ᵐ d ∂D, 0 ≤ d := by
  rw [ae_iff]; simp only [not_le]; exact hD0

/-- `I(q) = ∫_0^q F`. -/
lemma nv_leftover (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (hD0 : D (Set.Iio 0) = 0) (x : ℝ) :
    expLeftover D x = ∫ y in (0:ℝ)..x, cdf D y := by
  unfold expLeftover
  rcases le_or_gt 0 x with hx | hx
  · have hint : Integrable (fun d => max (x - d) 0) D := by
      refine Integrable.mono' (integrable_const x) ?_ ?_
      · exact (by fun_prop : Continuous fun d : ℝ => max (x-d) 0).aestronglyMeasurable
      · filter_upwards [nv_ae_nonneg D hD0] with d hd
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith) hx
    rw [hint.integral_eq_integral_Ioc_meas_le (M := x)
      (Filter.Eventually.of_forall fun d => le_max_right _ _)]
    · have h2 : ∫ t in Set.Ioc 0 x, D.real {a | t ≤ max (x - a) 0}
          = ∫ t in Set.Ioc 0 x, cdf D (x - t) := by
        refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
        have : {a : ℝ | t ≤ max (x - a) 0} = Set.Iic (x - t) := by
          ext a; simp only [Set.mem_setOf_eq, Set.mem_Iic]
          constructor
          · intro h; rcases le_max_iff.mp h with h | h
            · linarith
            · linarith [ht.1]
          · intro h; exact le_max_of_le_left (by linarith)
        rw [this, cdf_eq_real]
      rw [h2, ← intervalIntegral.integral_of_le hx, intervalIntegral.integral_comp_sub_left]
      simp
    · filter_upwards [nv_ae_nonneg D hD0] with d hd
      exact max_le (by linarith) hx
  · have h1 : ∫ d, max (x - d) 0 ∂D = 0 := by
      rw [integral_congr_ae (g := fun _ => (0:ℝ))]
      · simp
      filter_upwards [nv_ae_nonneg D hD0] with d hd
      exact max_eq_right (by linarith)
    have h2 : ∫ y in (0:ℝ)..x, cdf D y = ∫ y in (0:ℝ)..x, (0:ℝ) := by
      refine intervalIntegral.integral_congr ?_
      intro y hy
      rw [Set.uIcc_of_ge hx.le] at hy
      exact nv_cdf_nonpos D hD0 y (by linarith [hy.2])
    rw [h1, h2]; simp

lemma nv_int_min (D : Measure ℝ) [IsProbabilityMeasure D] (hD : Integrable (fun x => x) D)
    (q : ℝ) : Integrable (fun d => min q d) D := by
  refine Integrable.mono' ((integrable_const |q|).add hD.norm) ?_ ?_
  · exact (by fun_prop : Continuous fun d : ℝ => min q d).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun d => ?_)
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rcases le_total q d with h | h
    · rw [min_eq_left h]; linarith [abs_nonneg d]
    · rw [min_eq_right h]; linarith [abs_nonneg q]

lemma nv_int_max (D : Measure ℝ) [IsProbabilityMeasure D] (hD : Integrable (fun x => x) D)
    (q : ℝ) : Integrable (fun d => max (q - d) 0) D := by
  have : (fun d => max (q - d) 0) = fun d => q - min q d := by
    funext d; rcases le_total q d with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]
  rw [this]; exact (integrable_const q).sub (nv_int_min D hD q)

lemma nv_sales_leftover (D : Measure ℝ) [IsProbabilityMeasure D] (hD : Integrable (fun x => x) D)
    (q : ℝ) : expSales D q = q - expLeftover D q := by
  unfold expSales expLeftover
  have : (fun d => min q d) = fun d => q - max (q - d) 0 := by
    funext d; rcases le_total q d with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  rw [this, integral_sub (integrable_const q) (nv_int_max D hD q)]
  simp

lemma nv_sales (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (hD0 : D (Set.Iio 0) = 0) (q : ℝ) :
    expSales D q = q - ∫ y in (0:ℝ)..q, cdf D y := by
  rw [nv_sales_leftover D hD, nv_leftover D hD0]

lemma nv_lost (D : Measure ℝ) [IsProbabilityMeasure D] (hD : Integrable (fun x => x) D) (q : ℝ) :
    ∫ d, max (d - q) 0 ∂D = meanDemand D - expSales D q := by
  unfold meanDemand expSales
  have : (fun d => max (d - q) 0) = fun d => d - min q d := by
    funext d; rcases le_total q d with h | h
    · rw [min_eq_left h, max_eq_left (by linarith)]
    · rw [min_eq_right h, max_eq_right (by linarith)]; ring
  rw [this, integral_sub hD (nv_int_min D hD q)]

lemma nv_sales_le_mean (D : Measure ℝ) [IsProbabilityMeasure D] (hD : Integrable (fun x => x) D)
    (q : ℝ) : expSales D q ≤ meanDemand D := by
  unfold meanDemand expSales
  exact integral_mono (nv_int_min D hD q) hD (fun d => min_le_right _ _)

lemma nv_mean_nonneg (D : Measure ℝ) (hD0 : D (Set.Iio 0) = 0) : 0 ≤ meanDemand D := by
  unfold meanDemand
  exact integral_nonneg_of_ae (nv_ae_nonneg D hD0)

lemma nv_Phi_deriv (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D] (x : ℝ) :
    HasDerivAt (fun x => ∫ y in (0:ℝ)..x, cdf D y) (cdf D x) x :=
  ((nv_cdf_cont D).integral_hasStrictDerivAt 0 x).hasDerivAt

lemma nv_Phi_cont (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D] :
    Continuous (fun x => ∫ y in (0:ℝ)..x, cdf D y) :=
  continuous_iff_continuousAt.2 fun x => (nv_Phi_deriv D x).continuousAt

lemma nv_S_deriv (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (hD0 : D (Set.Iio 0) = 0) (q : ℝ) :
    HasDerivAt (expSales D) (1 - cdf D q) q := by
  have : expSales D = fun x => x - ∫ y in (0:ℝ)..x, cdf D y := funext (nv_sales D hD hD0)
  rw [this]
  exact (hasDerivAt_id q).sub (nv_Phi_deriv D q)

lemma nv_qf_int (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D] (δ q : ℝ) :
    ∫ y in (1 - δ) * q..q, cdf D y =
      (∫ y in (0:ℝ)..q, cdf D y) - ∫ y in (0:ℝ)..((1 - δ) * q), cdf D y := by
  rw [intervalIntegral.integral_interval_sub_left]
  · exact (nv_cdf_cont D).intervalIntegrable _ _
  · exact (nv_cdf_cont D).intervalIntegrable _ _

lemma nv_T_deriv (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (w δ q : ℝ) :
    HasDerivAt (quantityFlexTransfer P D w δ)
      (w - (w + P.cr - P.v) * (cdf D q - (1 - δ) * cdf D ((1 - δ) * q))) q := by
  have : quantityFlexTransfer P D w δ = fun q => w * q - (w + P.cr - P.v) *
      ((∫ y in (0:ℝ)..q, cdf D y) - ∫ y in (0:ℝ)..((1 - δ) * q), cdf D y) := by
    funext q; unfold quantityFlexTransfer; rw [nv_qf_int]
  rw [this]
  have h1 : HasDerivAt (fun q => ∫ y in (0:ℝ)..((1 - δ) * q), cdf D y)
      (cdf D ((1 - δ) * q) * (1 - δ)) q := by
    have := (nv_Phi_deriv D ((1 - δ) * q)).comp q ((hasDerivAt_id q).const_mul (1 - δ))
    exact this.congr_deriv (by simp)
  have h2 := ((hasDerivAt_id q).const_mul w).sub
    (((nv_Phi_deriv D q).sub h1).const_mul (w + P.cr - P.v))
  exact h2.congr_deriv (by ring)

lemma nv_R_deriv (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (hD0 : D (Set.Iio 0) = 0) (w δ q : ℝ) :
    HasDerivAt (retailerProfit P D (quantityFlexTransfer P D w δ))
      ((P.r - P.v + P.pr) * (1 - cdf D q) - (w + P.cr - P.v) *
        (1 - cdf D q + (1 - δ) * cdf D ((1 - δ) * q))) q := by
  have h := ((((nv_S_deriv D hD hD0 q).const_mul (P.r - P.v + P.pr)).sub
    ((hasDerivAt_id q).const_mul (P.cr - P.v))).sub_const (P.pr * meanDemand D)).sub
    (nv_T_deriv P D w δ q)
  unfold retailerProfit
  exact h.congr_deriv (by simp; ring)

lemma nv_Sup_deriv (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (hD0 : D (Set.Iio 0) = 0) (w δ q : ℝ) :
    HasDerivAt (supplierProfit P D (quantityFlexTransfer P D w δ))
      (P.ps * (1 - cdf D q) - P.cs + (w - (w + P.cr - P.v) *
        (cdf D q - (1 - δ) * cdf D ((1 - δ) * q)))) q := by
  have h := ((((nv_S_deriv D hD hD0 q).const_mul P.ps).sub
    ((hasDerivAt_id q).const_mul P.cs)).sub_const (P.ps * meanDemand D)).add
    (nv_T_deriv P D w δ q)
  unfold supplierProfit
  exact h.congr_deriv (by simp)

lemma nv_chain_deriv (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (hD0 : D (Set.Iio 0) = 0) (q : ℝ) :
    HasDerivAt (chainProfit P D)
      ((P.r - P.v + P.p) * (1 - cdf D q) - (P.c - P.v)) q := by
  have h := (((nv_S_deriv D hD hD0 q).const_mul (P.r - P.v + P.p)).sub
    ((hasDerivAt_id q).const_mul (P.c - P.v))).sub_const (P.p * meanDemand D)
  unfold chainProfit
  exact h.congr_deriv (by simp)

lemma nv_sum (P : ContractData) (D : Measure ℝ) (T : ℝ → ℝ) (q : ℝ) :
    retailerProfit P D T q + supplierProfit P D T q = chainProfit P D q := by
  unfold retailerProfit supplierProfit chainProfit ContractData.c ContractData.p; ring

lemma nv_params (P : ContractData) :
    0 < P.c - P.v ∧ P.c - P.v < P.r - P.v + P.p ∧ 0 < P.r - P.v + P.pr ∧
      P.r - P.v + P.p = P.r - P.v + P.pr + P.ps := by
  have h1 := P.profitable; have h2 := P.v_lt_c; have h3 := P.ps_nonneg; have h4 := P.pr_nonneg
  unfold ContractData.c ContractData.p
  refine ⟨by linarith, by linarith, by linarith, by ring⟩

/-- the critical fractile and positivity facts for a chain optimum -/
lemma nv_opt (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (hD0 : D (Set.Iio 0) = 0)
    (q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ q0) :
    1 - cdf D q0 = (P.c - P.v) / (P.r - P.v + P.p) ∧ 0 < 1 - cdf D q0 ∧ 0 < cdf D q0 ∧
      0 < q0 := by
  obtain ⟨p1, p2, p3, p4⟩ := nv_params P
  have hz := (h0.isLocalMax Filter.univ_mem).hasDerivAt_eq_zero (nv_chain_deriv P D hD hD0 q0)
  have hG : 0 < P.r - P.v + P.p := by linarith
  have e : 1 - cdf D q0 = (P.c - P.v) / (P.r - P.v + P.p) := by
    field_simp; linarith
  have ha : 0 < 1 - cdf D q0 := by rw [e]; positivity
  have hlt : (P.c - P.v) / (P.r - P.v + P.p) < 1 := by rw [div_lt_one hG]; exact p2
  have hF : 0 < cdf D q0 := by linarith
  refine ⟨e, ha, hF, ?_⟩
  by_contra hq; push Not at hq
  rw [nv_cdf_nonpos D hD0 q0 hq] at hF; exact lt_irrefl _ hF

/-- a function with antitone derivative vanishing at x0 is maximized there -/
lemma nv_max_of_antitone (f f' : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (f' x) x)
    (hmono : Antitone f') (x0 : ℝ) (hz : f' x0 = 0) : IsMaxOn f Set.univ x0 := by
  intro x _
  show f x ≤ f x0
  have hc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  rcases lt_trichotomy x x0 with h | h | h
  · obtain ⟨c, hc1, hc2⟩ := exists_hasDerivAt_eq_slope f f' h hc.continuousOn
      (fun y _ => hf y)
    have : 0 ≤ f' c := hz ▸ hmono hc1.2.le
    rw [hc2, le_div_iff₀ (by linarith)] at this
    linarith
  · rw [h]
  · obtain ⟨c, hc1, hc2⟩ := exists_hasDerivAt_eq_slope f f' h hc.continuousOn
      (fun y _ => hf y)
    have : f' c ≤ 0 := hz ▸ hmono hc1.1.le
    rw [hc2, div_le_iff₀ (by linarith)] at this
    linarith

lemma nv_wq0 (P : ContractData) (D : Measure ℝ) (q0 : ℝ) :
    quantityFlexPrice P D q0 0 = (P.r - P.v + P.pr) * (1 - cdf D q0) + P.v - P.cr := by
  unfold quantityFlexPrice; simp; ring

lemma nv_wq1 (P : ContractData) (D : Measure ℝ) (q0 : ℝ) (ha : 0 < 1 - cdf D q0) :
    quantityFlexPrice P D q0 1 = P.r + P.pr - P.cr := by
  unfold quantityFlexPrice; simp only [sub_self, zero_mul, add_zero]
  field_simp; ring

lemma nv_h_nonneg (D : Measure ℝ) (q0 δ : ℝ) (hδ1 : δ ≤ 1) :
    0 ≤ (1 - δ) * cdf D ((1 - δ) * q0) :=
  mul_nonneg (by linarith) (cdf_nonneg _ _)

lemma nv_W_eq (P : ContractData) (D : Measure ℝ) (q0 δ : ℝ) :
    quantityFlexPrice P D q0 δ + P.cr - P.v =
      (P.r - P.v + P.pr) * (1 - cdf D q0) / (1 - cdf D q0 + (1 - δ) * cdf D ((1 - δ) * q0)) := by
  unfold quantityFlexPrice; ring

lemma nv_W_bounds (P : ContractData) (D : Measure ℝ) (q0 δ : ℝ) (hδ1 : δ ≤ 1)
    (ha : 0 < 1 - cdf D q0) :
    0 ≤ quantityFlexPrice P D q0 δ + P.cr - P.v ∧
      quantityFlexPrice P D q0 δ + P.cr - P.v ≤ P.r - P.v + P.pr := by
  obtain ⟨p1, p2, p3, p4⟩ := nv_params P
  have hh := nv_h_nonneg D q0 δ hδ1
  rw [nv_W_eq]
  constructor
  · positivity
  · rw [div_le_iff₀ (by linarith)]; nlinarith

theorem eq_2_core (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D]
    [NullSingletonClass D] (hD : Integrable (fun x => x) D)
    (hD0 : D (Set.Iio 0) = 0)
    (hF : ∀ x y : ℝ, 0 ≤ x → x < y → cdf D x < 1 → cdf D x < cdf D y)
    (q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ q0) :
    1 - cdf D q0 = (P.c - P.v) / (P.r - P.v + P.p) ∧
      ∀ q : ℝ, IsMaxOn (chainProfit P D) Set.univ q → q = q0 := by
  obtain ⟨e0, a0, f0, q0p⟩ := nv_opt P D hD hD0 q0 h0
  refine ⟨e0, fun q hq => ?_⟩
  obtain ⟨e1, a1, f1, q1p⟩ := nv_opt P D hD hD0 q hq
  rcases lt_trichotomy q q0 with h | h | h
  · have := hF q q0 q1p.le h (by linarith); linarith
  · exact h
  · have := hF q0 q q0p.le h (by linarith); linarith

theorem p24_core (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (hD0 : D (Set.Iio 0) = 0)
    (hF : ∀ x y : ℝ, 0 ≤ x → x < y → cdf D x < 1 → cdf D x < cdf D y)
    (q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ q0) :
    quantityFlexPrice P D q0 0 = (P.r - P.v + P.pr) * (1 - cdf D q0) + P.v - P.cr ∧
      quantityFlexPrice P D q0 1 = P.r + P.pr - P.cr ∧
      StrictMonoOn (fun δ => quantityFlexPrice P D q0 δ) (Set.Icc 0 1) ∧
      ∀ δ ∈ Set.Icc (0 : ℝ) 1,
        P.v - P.cr ≤ quantityFlexPrice P D q0 δ ∧ quantityFlexPrice P D q0 δ ≤ P.r + P.pr - P.cr := by
  obtain ⟨e0, a0, f0, q0p⟩ := nv_opt P D hD hD0 q0 h0
  obtain ⟨p1, p2, p3, p4⟩ := nv_params P
  refine ⟨nv_wq0 P D q0, nv_wq1 P D q0 a0, ?_, ?_⟩
  · intro d1 hd1 d2 hd2 hlt
    simp only
    have F00 : cdf D 0 = 0 := nv_cdf_nonpos D hD0 0 le_rfl
    have hx1 : 0 < (1 - d1) * q0 := mul_pos (by linarith [hd2.2]) q0p
    have Fx1 : 0 < cdf D ((1 - d1) * q0) := by
      have := hF 0 _ le_rfl hx1 (by rw [F00]; norm_num); linarith
    have Fmono : cdf D ((1 - d2) * q0) ≤ cdf D ((1 - d1) * q0) :=
      monotone_cdf D (by nlinarith)
    have hh : (1 - d2) * cdf D ((1 - d2) * q0) < (1 - d1) * cdf D ((1 - d1) * q0) := by
      have := hd2.2
      calc (1 - d2) * cdf D ((1 - d2) * q0) ≤ (1 - d2) * cdf D ((1 - d1) * q0) :=
            mul_le_mul_of_nonneg_left Fmono (by linarith)
        _ < (1 - d1) * cdf D ((1 - d1) * q0) := by nlinarith
    have hn2 := nv_h_nonneg D q0 d2 hd2.2
    have key : (P.r - P.v + P.pr) * (1 - cdf D q0) /
          (1 - cdf D q0 + (1 - d1) * cdf D ((1 - d1) * q0)) <
        (P.r - P.v + P.pr) * (1 - cdf D q0) /
          (1 - cdf D q0 + (1 - d2) * cdf D ((1 - d2) * q0)) :=
      div_lt_div_of_pos_left (by positivity) (by linarith) (by linarith)
    have e1 := nv_W_eq P D q0 d1
    have e2 := nv_W_eq P D q0 d2
    linarith
  · intro δ hδ
    have := nv_W_bounds P D q0 δ hδ.2 a0
    constructor <;> linarith [this.1, this.2]

theorem eq_11_core (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D]
    [NullSingletonClass D] (hD : Integrable (fun x => x) D)
    (hD0 : D (Set.Iio 0) = 0)
    (q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ q0)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    HasDerivAt (retailerProfit P D
      (quantityFlexTransfer P D (quantityFlexPrice P D q0 δ) δ)) 0 q0 ∧
    IsMaxOn (retailerProfit P D
      (quantityFlexTransfer P D (quantityFlexPrice P D q0 δ) δ)) Set.univ q0 := by
  obtain ⟨e0, a0, f0, q0p⟩ := nv_opt P D hD hD0 q0 h0
  obtain ⟨p1, p2, p3, p4⟩ := nv_params P
  obtain ⟨W0, W1⟩ := nv_W_bounds P D q0 δ hδ1 a0
  have hh := nv_h_nonneg D q0 δ hδ1
  have hz : (P.r - P.v + P.pr) * (1 - cdf D q0) - (quantityFlexPrice P D q0 δ + P.cr - P.v) *
        (1 - cdf D q0 + (1 - δ) * cdf D ((1 - δ) * q0)) = 0 := by
    rw [nv_W_eq]; field_simp; ring
  refine ⟨(nv_R_deriv P D hD hD0 _ δ q0).congr_deriv hz, ?_⟩
  refine nv_max_of_antitone _ _ (fun q => nv_R_deriv P D hD hD0 _ δ q) ?_ q0 hz
  intro x y hxy
  simp only
  have m1 : cdf D x ≤ cdf D y := monotone_cdf D hxy
  have m2 : cdf D ((1 - δ) * x) ≤ cdf D ((1 - δ) * y) :=
    monotone_cdf D (mul_le_mul_of_nonneg_left hxy (by linarith))
  have k1 : (P.r - P.v + P.pr - (quantityFlexPrice P D q0 δ + P.cr - P.v)) * cdf D x ≤
      (P.r - P.v + P.pr - (quantityFlexPrice P D q0 δ + P.cr - P.v)) * cdf D y :=
    mul_le_mul_of_nonneg_left m1 (by linarith)
  have k2 : (quantityFlexPrice P D q0 δ + P.cr - P.v) * ((1 - δ) * cdf D ((1 - δ) * x)) ≤
      (quantityFlexPrice P D q0 δ + P.cr - P.v) * ((1 - δ) * cdf D ((1 - δ) * y)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left m2 (by linarith)) W0
  nlinarith

theorem p25_supplier_foc_core (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D]
    [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (hD0 : D (Set.Iio 0) = 0)
    (q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ q0)
    (δ : ℝ) (hδ1 : δ ≤ 1) :
    HasDerivAt
        (supplierProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 δ) δ))
        (P.ps * (1 - cdf D q0) - P.c + P.v + (P.r - P.v + P.pr) * (1 - cdf D q0)) q0 ∧
      P.ps * (1 - cdf D q0) - P.c + P.v + (P.r - P.v + P.pr) * (1 - cdf D q0) = 0 := by
  obtain ⟨e0, a0, f0, q0p⟩ := nv_opt P D hD hD0 q0 h0
  obtain ⟨p1, p2, p3, p4⟩ := nv_params P
  have hh := nv_h_nonneg D q0 δ hδ1
  refine ⟨(nv_Sup_deriv P D hD hD0 _ δ q0).congr_deriv ?_, ?_⟩
  · have hW := nv_W_eq P D q0 δ
    have hWa : (quantityFlexPrice P D q0 δ + P.cr - P.v) *
        (1 - cdf D q0 + (1 - δ) * cdf D ((1 - δ) * q0)) = (P.r - P.v + P.pr) * (1 - cdf D q0) := by
      rw [hW]; field_simp
    unfold ContractData.c at *
    linear_combination hWa
  · have hG : 0 < P.r - P.v + P.p := by linarith
    have : (P.r - P.v + P.p) * (1 - cdf D q0) = P.c - P.v := by rw [e0]; field_simp
    linear_combination this - (1 - cdf D q0) * p4

lemma nv_R0 (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D]
    [NullSingletonClass D] (q0 : ℝ) :
    retailerProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 0) 0) q0 =
      (P.r - P.v + P.pr) * expSales D q0 - (P.r - P.v + P.pr) * (1 - cdf D q0) * q0
        - P.pr * meanDemand D := by
  unfold retailerProfit quantityFlexTransfer
  rw [nv_wq0]; simp only [sub_zero, one_mul, intervalIntegral.integral_same]; ring

lemma nv_Sup1 (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D]
    [NullSingletonClass D] (q0 : ℝ) (ha : 0 < 1 - cdf D q0) :
    supplierProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 1) 1) q0 =
      P.ps * expSales D q0 - P.cs * q0 - P.ps * meanDemand D + (P.r + P.pr - P.cr) * q0
        - (P.r - P.v + P.pr) * ∫ y in (0:ℝ)..q0, cdf D y := by
  unfold supplierProfit quantityFlexTransfer
  rw [nv_wq1 P D q0 ha]; simp only [sub_self, zero_mul]; ring

theorem p25_delta_zero_core (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D]
    [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (hD0 : D (Set.Iio 0) = 0)
    (q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ q0) :
    retailerProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 0) 0) q0 =
        (P.r - P.v + P.pr) * expSales D q0
          - (P.r - P.v + P.pr) / (P.r - P.v + P.p) * (P.c - P.v) * q0 - meanDemand D * P.pr ∧
      retailerProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 0) 0) q0 =
        chainProfit P D q0 + P.ps * (meanDemand D - expSales D q0 + (1 - cdf D q0) * q0) ∧
      chainProfit P D q0 ≤
        retailerProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 0) 0) q0 := by
  obtain ⟨e0, a0, f0, q0p⟩ := nv_opt P D hD hD0 q0 h0
  obtain ⟨p1, p2, p3, p4⟩ := nv_params P
  have hG : 0 < P.r - P.v + P.p := by linarith
  have hS := nv_sales_le_mean D hD q0
  have e2 : retailerProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 0) 0) q0 =
        chainProfit P D q0 + P.ps * (meanDemand D - expSales D q0 + (1 - cdf D q0) * q0) := by
    rw [nv_R0]; unfold chainProfit ContractData.p ContractData.c at *
    have : (P.r - P.v + (P.ps + P.pr)) * (1 - cdf D q0) = P.cs + P.cr - P.v := by
      rw [e0]; field_simp
    linear_combination (-q0) * this
  refine ⟨?_, e2, ?_⟩
  · rw [nv_R0, e0]; ring
  · rw [e2]
    have : 0 ≤ P.ps * (meanDemand D - expSales D q0 + (1 - cdf D q0) * q0) :=
      mul_nonneg P.ps_nonneg (by nlinarith)
    linarith

theorem p25_delta_one_core (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D]
    [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (hD0 : D (Set.Iio 0) = 0)
    (q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ q0) :
    supplierProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 1) 1) q0 =
        P.ps * expSales D q0 + (P.r + P.pr - P.c) * q0
          - (P.r + P.pr - P.v) * (∫ y in (0 : ℝ)..q0, cdf D y) - meanDemand D * P.ps ∧
      supplierProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 1) 1) q0 =
        chainProfit P D q0 + meanDemand D * P.pr ∧
      chainProfit P D q0 ≤
        supplierProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 1) 1) q0 := by
  obtain ⟨e0, a0, f0, q0p⟩ := nv_opt P D hD hD0 q0 h0
  have e2 : supplierProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 1) 1) q0 =
        chainProfit P D q0 + meanDemand D * P.pr := by
    rw [nv_Sup1 P D q0 a0]
    have hS := nv_sales D hD hD0 q0
    unfold chainProfit ContractData.p ContractData.c
    linear_combination (-(P.r - P.v + P.pr)) * hS
  refine ⟨?_, e2, ?_⟩
  · rw [nv_Sup1 P D q0 a0]; unfold ContractData.c; ring
  · rw [e2]; have := mul_nonneg (nv_mean_nonneg D hD0) P.pr_nonneg; linarith

theorem p25_qf_allocation_core (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D]
    [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (hD0 : D (Set.Iio 0) = 0)
    (q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ q0) :
    (retailerProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 0) 0) q0 =
        chainProfit P D q0 + P.ps * (meanDemand D - expSales D q0 + (1 - cdf D q0) * q0) ∧
      chainProfit P D q0 ≤
        retailerProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 0) 0) q0) ∧
    (supplierProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 1) 1) q0 =
        chainProfit P D q0 + meanDemand D * P.pr ∧
      chainProfit P D q0 ≤
        supplierProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 1) 1) q0) ∧
    ∀ a ∈ Set.Icc 0 (chainProfit P D q0), ∃ δ ∈ Set.Icc (0 : ℝ) 1,
      retailerProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 δ) δ) q0 = a ∧
      supplierProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 δ) δ) q0 =
        chainProfit P D q0 - a := by
  obtain ⟨z1, z2, z3⟩ := p25_delta_zero_core P D hD hD0 q0 h0
  obtain ⟨o1, o2, o3⟩ := p25_delta_one_core P D hD hD0 q0 h0
  obtain ⟨e0, a0, f0, q0p⟩ := nv_opt P D hD hD0 q0 h0
  refine ⟨⟨z2, z3⟩, ⟨o2, o3⟩, ?_⟩
  intro a ha
  let f : ℝ → ℝ := fun δ =>
    retailerProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 δ) δ) q0
  have hden : ∀ δ ∈ Set.Icc (0:ℝ) 1,
      1 - cdf D q0 + (1 - δ) * cdf D ((1 - δ) * q0) ≠ 0 := by
    intro δ hδ; have := nv_h_nonneg D q0 δ hδ.2; linarith
  have hwc : ContinuousOn (fun δ => quantityFlexPrice P D q0 δ) (Set.Icc 0 1) := by
    unfold quantityFlexPrice
    have hc : Continuous (fun δ : ℝ => 1 - cdf D q0 + (1 - δ) * cdf D ((1 - δ) * q0)) := by
      have := nv_cdf_cont D; fun_prop
    exact ((continuousOn_const.div hc.continuousOn hden).sub continuousOn_const).add
      continuousOn_const
  have hfc : ContinuousOn f (Set.Icc 0 1) := by
    have hPhi : Continuous (fun δ : ℝ => ∫ y in (1 - δ) * q0..q0, cdf D y) := by
      have : (fun δ : ℝ => ∫ y in (1 - δ) * q0..q0, cdf D y) = fun δ =>
          (∫ y in (0:ℝ)..q0, cdf D y) - ∫ y in (0:ℝ)..((1 - δ) * q0), cdf D y := by
        funext δ; exact nv_qf_int D δ q0
      rw [this]
      have := nv_Phi_cont D
      exact continuous_const.sub (this.comp (by fun_prop))
    show ContinuousOn (fun δ => retailerProfit P D
      (quantityFlexTransfer P D (quantityFlexPrice P D q0 δ) δ) q0) (Set.Icc 0 1)
    unfold retailerProfit quantityFlexTransfer
    exact continuousOn_const.sub ((hwc.mul continuousOn_const).sub
      (((hwc.add continuousOn_const).sub continuousOn_const).mul hPhi.continuousOn))
  have h1 : f 1 ≤ a := by
    have := nv_sum P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 1) 1) q0
    show retailerProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 1) 1) q0 ≤ a
    have := mul_nonneg (nv_mean_nonneg D hD0) P.pr_nonneg
    linarith [ha.1]
  have h2 : a ≤ f 0 := le_trans ha.2 z3
  obtain ⟨δ, hδ, hfδ⟩ := intermediate_value_Icc' (zero_le_one' ℝ) hfc ⟨h1, h2⟩
  refine ⟨δ, hδ, hfδ, ?_⟩
  have := nv_sum P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 δ) δ) q0
  have hf : f δ = retailerProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 δ) δ) q0 :=
    rfl
  linarith

end CachonCoord.Newsvendor

open CachonCoord.Newsvendor


theorem solution (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (hD0 : D (Set.Iio 0) = 0)
    (hF : ∀ x y : ℝ, 0 ≤ x → x < y → cdf D x < 1 → cdf D x < cdf D y)
    (density : ℝ → ℝ)
    (hFderiv : ∀ x : ℝ, 0 < x → cdf D x < 1 → HasDerivAt (cdf D) (density x) x)
    (q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ q0)
    (hPi : 0 < chainProfit P D q0)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    HasDerivAt
        (supplierProfit P D (quantityFlexTransfer P D (quantityFlexPrice P D q0 δ) δ))
        (P.ps * (1 - cdf D q0) - P.c + P.v + (P.r - P.v + P.pr) * (1 - cdf D q0)) q0 ∧
      P.ps * (1 - cdf D q0) - P.c + P.v + (P.r - P.v + P.pr) * (1 - cdf D q0) = 0 := by
  exact p25_supplier_foc_core P D hD hD0 q0 h0 δ hδ1

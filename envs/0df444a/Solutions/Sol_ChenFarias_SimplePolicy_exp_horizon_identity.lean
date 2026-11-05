-- Prove2me | solution 1 for ChenFarias.SimplePolicy.exp_horizon_identity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T18:56:59.280403+00:00
-- url     : https://prove2.me/submissions/8a3a1b82-abf1-48f5-8cb2-14a823715b00

import Mathlib
import Definitions.Def_ChenFarias_SimplePolicy_Model
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
open ChenFarias.SimplePolicy

lemma cf_lintegral_expMeasure (β : ℝ) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ s, g s ∂expMeasure β =
      ∫⁻ s in Ici 0, ENNReal.ofReal (β * Real.exp (-(β * s))) * g s := by
  have hpdf : Measurable (exponentialPDF β) :=
    (measurable_exponentialPDFReal β).ennreal_ofReal
  have : expMeasure β = volume.withDensity (exponentialPDF β) := rfl
  rw [this, lintegral_withDensity_eq_lintegral_mul _ hpdf hg]
  have hind : (exponentialPDF β * g) =
      (Ici (0:ℝ)).indicator (fun s => ENNReal.ofReal (β * Real.exp (-(β * s))) * g s) := by
    funext s
    by_cases hs : 0 ≤ s
    · simp [Set.indicator_of_mem (show s ∈ Ici (0:ℝ) from hs), exponentialPDF_of_nonneg hs]
    · push Not at hs
      simp [Set.indicator_of_notMem (show s ∉ Ici (0:ℝ) from not_le.2 hs),
        exponentialPDF_of_neg hs]
  rw [hind, lintegral_indicator measurableSet_Ici]

lemma cf_lintegral_Ioi_FTC {g g' : ℝ → ℝ} {a l : ℝ}
    (hderiv : ∀ x ∈ Ici a, HasDerivAt g (g' x) x) (hpos : ∀ x ∈ Ioi a, 0 ≤ g' x)
    (hg : Tendsto g atTop (𝓝 l)) :
    ∫⁻ x in Ioi a, ENNReal.ofReal (g' x) = ENNReal.ofReal (l - g a) := by
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hg
  rw [← integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hg,
    ofReal_integral_eq_lintegral_ofReal hint]
  exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hpos)

lemma cf_expMeasure_Iio (r : ℝ) : expMeasure r (Iio 0) = 0 := by
  have : expMeasure r = volume.withDensity (exponentialPDF r) := rfl
  rw [this, withDensity_apply _ measurableSet_Iio]
  rw [setLIntegral_congr_fun measurableSet_Iio (g := fun _ => 0)
    (fun x hx => exponentialPDF_of_neg hx)]
  simp

/-- Tail of the exponential law. -/
lemma cf_expMeasure_Ici (β a : ℝ) (hβ : 0 < β) (ha : 0 ≤ a) :
    expMeasure β (Ici a) = ENNReal.ofReal (Real.exp (-(β * a))) := by
  rw [← lintegral_indicator_one measurableSet_Ici,
    cf_lintegral_expMeasure β (g := (Ici a).indicator 1)
      ((measurable_const).indicator measurableSet_Ici)]
  have h1 : (fun s => ENNReal.ofReal (β * Real.exp (-(β * s))) * (Ici a).indicator 1 s) =
      (Ici a).indicator (fun s => ENNReal.ofReal (β * Real.exp (-(β * s)))) := by
    funext s
    by_cases hs : s ∈ Ici a
    · simp [Set.indicator_of_mem hs]
    · simp [Set.indicator_of_notMem hs]
  rw [h1, lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    show Ici a ∩ Ici (0:ℝ) = Ici a from inter_eq_left.2 (Ici_subset_Ici.2 ha),
    ← setLIntegral_congr Ioi_ae_eq_Ici]
  have hderiv : ∀ x ∈ Ici a, HasDerivAt (fun s => -Real.exp (-(β * s)))
      (β * Real.exp (-(β * x))) x := by
    intro x _
    have := (((hasDerivAt_id x).const_mul β).neg.exp).neg
    refine this.congr_deriv ?_
    simp only [Pi.neg_apply, id, mul_one]; ring
  have hpos : ∀ x ∈ Ioi a, 0 ≤ β * Real.exp (-(β * x)) := fun x _ => by positivity
  have htend : Tendsto (fun s => -Real.exp (-(β * s))) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hβ)
    simpa [Function.comp_def] using this.neg
  rw [cf_lintegral_Ioi_FTC hderiv hpos htend]
  congr 1; ring

lemma cf_clock_ae_nonneg (x0 : ℕ) : ∀ᵐ e ∂clockLaw x0, ∀ i, 0 ≤ e i := by
  rw [ae_all_iff]
  intro i
  have h : ∀ᵐ y ∂expMeasure 1, 0 ≤ y := by
    rw [ae_iff]
    have := cf_expMeasure_Iio 1
    simpa [not_le, Iio] using this
  have : IsProbabilityMeasure (expMeasure (1:ℝ)) := isProbabilityMeasure_expMeasure one_pos
  exact Measure.tendsto_eval_ae_ae.eventually h

lemma cf_saleTime_measurable (lam : ℝ) (f : ℝ → ℝ) (π : ℕ → ℝ) (x0 k : ℕ) :
    Measurable (saleTime lam f π x0 k) := by
  unfold saleTime
  exact Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).div_const _)

lemma cf_saleTime_nonneg (lam : ℝ) (f : ℝ → ℝ) (π : ℕ → ℝ) (x0 k : ℕ)
    (hlam : 0 < lam) (hf : Assumption1 f) (e : Fin x0 → ℝ) (he : ∀ i, 0 ≤ e i) :
    0 ≤ saleTime lam f π x0 k e := by
  unfold saleTime
  refine Finset.sum_nonneg (fun i _ => div_nonneg (he i) (mul_nonneg hlam.le ?_))
  exact setIntegral_nonneg measurableSet_Ioi (fun v _ => hf.nonnegative v)

lemma cf_clockLaw_prob (x0 : ℕ) : IsProbabilityMeasure (clockLaw x0) := by
  have : IsProbabilityMeasure (expMeasure (1:ℝ)) := isProbabilityMeasure_expMeasure one_pos
  unfold clockLaw
  infer_instance

theorem solution (lam β : ℝ) (f : ℝ → ℝ) (V : ℕ → ℝ)
    (π : ℕ → ℝ) (x0 : ℕ) (hlam : 0 < lam) (hβ : 0 < β)
    (hf : Assumption1 f) (hV : IsValueFn lam β f V)
    (hπ : IsRootPolicy f V π) :
    (∫⁻ e, ENNReal.ofReal (discRevenue lam f π x0 β e) ∂clockLaw x0) =
      ∫⁻ s, J lam f π x0 s ∂expMeasure β := by
  have hπ0 : ∀ k ∈ Finset.Icc 1 x0, 0 ≤ π (x0 - k + 1) := by
    intro k hk
    have := Finset.mem_Icc.1 hk
    exact (hπ _ (by omega)).1
  have hS := cf_saleTime_measurable lam f π x0
  have hmeas : Measurable (Function.uncurry fun (s : ℝ) (e : Fin x0 → ℝ) =>
      ENNReal.ofReal (revenueBy lam f π x0 s e)) := by
    unfold revenueBy
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_sum
    intro k _
    exact Measurable.ite (measurableSet_le ((hS k).comp measurable_snd) measurable_fst)
      measurable_const measurable_const
  have := cf_clockLaw_prob x0
  have := isProbabilityMeasure_expMeasure hβ
  unfold J
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [cf_clock_ae_nonneg x0] with e he
  have hrev : ∀ s, ENNReal.ofReal (revenueBy lam f π x0 s e) =
      ∑ k ∈ Finset.Icc 1 x0, (Ici (saleTime lam f π x0 k e)).indicator
        (fun _ => ENNReal.ofReal (π (x0 - k + 1))) s := by
    intro s
    unfold revenueBy
    rw [ENNReal.ofReal_sum_of_nonneg (fun k hk => by
      split_ifs
      · exact hπ0 k hk
      · exact le_rfl)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases h : saleTime lam f π x0 k e ≤ s
    · rw [if_pos h, indicator_of_mem (show s ∈ Ici _ from h)]
    · rw [if_neg h, indicator_of_notMem (show s ∉ Ici _ from h), ENNReal.ofReal_zero]
  simp_rw [hrev]
  rw [lintegral_finsetSum _ (fun k _ => measurable_const.indicator measurableSet_Ici)]
  simp_rw [lintegral_indicator_const measurableSet_Ici]
  unfold discRevenue
  rw [ENNReal.ofReal_sum_of_nonneg (fun k hk => mul_nonneg (hπ0 k hk) (Real.exp_pos _).le)]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [cf_expMeasure_Ici β _ hβ (cf_saleTime_nonneg lam f π x0 k hlam hf e he),
    ENNReal.ofReal_mul (hπ0 k hk)]

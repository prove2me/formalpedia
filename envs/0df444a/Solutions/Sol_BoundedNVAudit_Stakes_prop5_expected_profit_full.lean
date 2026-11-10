-- Prove2me | solution 1 for BoundedNVAudit.Stakes.prop5_expected_profit_full
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T08:22:42.294342+00:00
-- url     : https://prove2.me/submissions/94bcf3e9-972b-4b9a-afd2-ca94a596967d

import Mathlib
import Definitions.Def_BoundedNVAudit_Stakes_GeneralDemand
import Definitions.Def_BoundedNVAudit_Stakes_LogitLaw
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P01

set_option autoImplicit false

open MeasureTheory Filter Topology
open QAlgorithms.Papers.Independent.Next46.P01 (extendedExpectation)

/-! ## Demand-side lemmas (general real demand) -/

open BoundedNVAudit.Stakes BoundedNV.Uniform in
lemma z7_minf_int (f : ℝ → ℝ) (hf : IsGeneralDemandDensity f) (v : ℝ) :
    Integrable (fun t => min t v * f t) := by
  have hdom : Integrable (fun t => |v| * f t + max (-t) 0 * f t) :=
    (hf.integrable.const_mul |v|).add hf.negative_part
  refine Integrable.mono' hdom ?_ ?_
  · exact ((continuous_id.min continuous_const).aestronglyMeasurable).mul
      hf.integrable.aestronglyMeasurable
  · refine Eventually.of_forall (fun t => ?_)
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hf.nonneg t)]
    have h3 : 0 ≤ max (-t) 0 := le_max_right _ _
    have h3' : -t ≤ max (-t) 0 := le_max_left _ _
    have h4 : 0 ≤ |v| := abs_nonneg v
    have habs : |min t v| ≤ |v| + max (-t) 0 := by
      rw [abs_le]; constructor
      · have h1 : -|v| ≤ v := neg_abs_le v
        rcases le_total t v with h | h
        · rw [min_eq_left h]; linarith
        · rw [min_eq_right h]; linarith
      · linarith [min_le_right t v, le_abs_self v]
    calc |min t v| * f t ≤ (|v| + max (-t) 0) * f t :=
          mul_le_mul_of_nonneg_right habs (hf.nonneg t)
      _ = |v| * f t + max (-t) 0 * f t := by ring

open BoundedNVAudit.Stakes BoundedNV.Uniform in
lemma z7_cont (f : ℝ → ℝ) (hf : IsGeneralDemandDensity f) (p c : ℝ) :
    Continuous (nvProfit f p c) := by
  have hL : ∀ x y, |expMin f x - expMin f y| ≤ |x - y| := by
    intro x y
    unfold expMin
    rw [← integral_sub (z7_minf_int f hf _) (z7_minf_int f hf _)]
    have hb : Integrable (fun t => |x - y| * f t) := hf.integrable.const_mul _
    calc |∫ t, (min t x * f t - min t y * f t)|
        ≤ ∫ t, |x - y| * f t := by
          rw [← Real.norm_eq_abs]
          refine norm_integral_le_of_norm_le hb (Eventually.of_forall (fun t => ?_))
          rw [Real.norm_eq_abs, ← sub_mul, abs_mul, abs_of_nonneg (hf.nonneg t)]
          refine mul_le_mul_of_nonneg_right ?_ (hf.nonneg t)
          have := abs_min_sub_min_le_max t x t y
          simpa using this
      _ = |x - y| := by rw [integral_const_mul, hf.mass_one, mul_one]
  have hc : Continuous (expMin f) := by
    refine (LipschitzWith.of_dist_le_mul (K := 1) (fun x y => ?_)).continuous
    simpa [Real.dist_eq] using hL x y
  unfold nvProfit
  fun_prop

lemma z7_S_meas (f : ℝ → ℝ) : MeasurableSet (BoundedNV.ExpFam.decisionDomain f) :=
  ((convex_convexHull ℝ _).ordConnected).measurableSet

lemma z7_f_off (f : ℝ → ℝ) (x : ℝ) (hx : x ∉ BoundedNV.ExpFam.decisionDomain f) : f x = 0 := by
  by_contra h
  exact hx (subset_convexHull ℝ _ h)

open BoundedNVAudit.Stakes BoundedNV.Uniform in
lemma z7_m_le_self (f : ℝ → ℝ) (hf : IsGeneralDemandDensity f) (y : ℝ) : expMin f y ≤ y := by
  unfold expMin
  calc ∫ t, min t y * f t ≤ ∫ t, y * f t :=
        integral_mono (z7_minf_int f hf y) (hf.integrable.const_mul y)
          (fun t => mul_le_mul_of_nonneg_right (min_le_right t y) (hf.nonneg t))
    _ = y := by rw [integral_const_mul, hf.mass_one, mul_one]

open BoundedNVAudit.Stakes BoundedNV.Uniform in
lemma z7_m_diff_le (f : ℝ → ℝ) (hf : IsGeneralDemandDensity f) {x y : ℝ} (hxy : x ≤ y) :
    expMin f y - expMin f x ≤ (y - x) * ∫ t, (Set.Ioi x).indicator f t := by
  unfold expMin
  rw [← integral_sub (z7_minf_int f hf y) (z7_minf_int f hf x), ← integral_const_mul]
  refine integral_mono ((z7_minf_int f hf y).sub (z7_minf_int f hf x))
    ((hf.integrable.indicator measurableSet_Ioi).const_mul _) (fun t => ?_)
  dsimp only
  by_cases ht : x < t
  · rw [Set.indicator_of_mem (show t ∈ Set.Ioi x from ht), min_eq_right ht.le, ← sub_mul]
    exact mul_le_mul_of_nonneg_right (by linarith [min_le_right t y]) (hf.nonneg t)
  · push_neg at ht
    rw [Set.indicator_of_notMem (show t ∉ Set.Ioi x from fun h => absurd h (not_lt.mpr ht)),
      min_eq_left ht, min_eq_left (ht.trans hxy)]
    simp

open BoundedNVAudit.Stakes BoundedNV.Uniform in
lemma z7_m_diff_ge (f : ℝ → ℝ) (hf : IsGeneralDemandDensity f) {x y : ℝ} (hxy : x ≤ y) :
    (y - x) * ∫ t, (Set.Ioi y).indicator f t ≤ expMin f y - expMin f x := by
  unfold expMin
  rw [← integral_sub (z7_minf_int f hf y) (z7_minf_int f hf x), ← integral_const_mul]
  refine integral_mono ((hf.integrable.indicator measurableSet_Ioi).const_mul _)
    ((z7_minf_int f hf y).sub (z7_minf_int f hf x)) (fun t => ?_)
  dsimp only
  by_cases ht : y < t
  · rw [Set.indicator_of_mem (show t ∈ Set.Ioi y from ht), min_eq_right ht.le,
      min_eq_right (hxy.trans ht.le)]
    ring_nf
    exact le_refl _
  · rw [Set.indicator_of_notMem (show t ∉ Set.Ioi y from ht), mul_zero, ← sub_mul]
    exact mul_nonneg (sub_nonneg.mpr (min_le_min_left t hxy)) (hf.nonneg t)

open BoundedNVAudit.Stakes BoundedNV.Uniform in
lemma z7_tail (f : ℝ → ℝ) (hf : IsGeneralDemandDensity f) :
    Tendsto (fun a : ℝ => ∫ t, (Set.Ioi a).indicator f t) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
    (F := fun a : ℝ => (Set.Ioi a).indicator f) (f := fun _ => (0:ℝ)) (fun t => ‖f t‖)
    (Eventually.of_forall (fun a =>
      (hf.integrable.indicator measurableSet_Ioi).aestronglyMeasurable))
    (Eventually.of_forall (fun a => Eventually.of_forall (fun t =>
      norm_indicator_le_norm_self _ _)))
    hf.integrable.norm
    (Eventually.of_forall (fun t => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop t] with a ha
      rw [Set.indicator_of_notMem (by simpa using ha)]))
  simpa using h

open BoundedNVAudit.Stakes BoundedNV.Uniform in
lemma z7_upper (f : ℝ → ℝ) (hf : IsGeneralDemandDensity f) (p c : ℝ) (hc : 0 < c)
    (hcp : c < p) : ∃ A κ : ℝ, 0 < κ ∧ ∀ y, nvProfit f p c y ≤ A - κ * |y| := by
  have hp : 0 < p := hc.trans hcp
  obtain ⟨x₀, hx₀, hT⟩ : ∃ x₀ : ℝ, 0 ≤ x₀ ∧ ∫ t, (Set.Ioi x₀).indicator f t ≤ c / (2 * p) := by
    have hlim := z7_tail f hf
    have hev := hlim.eventually (ge_mem_nhds (show (0:ℝ) < c / (2 * p) by positivity))
    obtain ⟨x, hx⟩ := (hev.and (eventually_ge_atTop 0)).exists
    exact ⟨x, hx.2, hx.1⟩
  have hκ1 : min (p - c) (c / 2) ≤ p - c := min_le_left _ _
  have hκ2 : min (p - c) (c / 2) ≤ c / 2 := min_le_right _ _
  have hκ0 : 0 < min (p - c) (c / 2) := lt_min (by linarith) (by linarith)
  refine ⟨2 * (p - c) * x₀ + |nvProfit f p c x₀| + c / 2 * x₀, min (p - c) (c / 2), hκ0,
    fun y => ?_⟩
  have hab := le_abs_self (nvProfit f p c x₀)
  have h3 : 0 ≤ |nvProfit f p c x₀| := abs_nonneg _
  have h4 : 0 ≤ (p - c) * x₀ := mul_nonneg (by linarith) hx₀
  have h5 : 0 ≤ c / 2 * x₀ := mul_nonneg (by linarith) hx₀
  unfold nvProfit at hab h3 ⊢
  rcases le_or_gt y x₀ with hy | hy
  · have hm := z7_m_le_self f hf y
    have h1 : p * expMin f y ≤ p * y := mul_le_mul_of_nonneg_left hm hp.le
    rcases le_or_gt y 0 with hy0 | hy0
    · rw [abs_of_nonpos hy0]
      have h2 : (p - c - min (p - c) (c / 2)) * y ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) hy0
      linarith
    · rw [abs_of_pos hy0]
      have h2 : min (p - c) (c / 2) * y ≤ (p - c) * x₀ :=
        mul_le_mul hκ1 hy hy0.le (by linarith)
      have h6 : (p - c) * y ≤ (p - c) * x₀ := mul_le_mul_of_nonneg_left hy (by linarith)
      linarith
  · have hd := z7_m_diff_le f hf hy.le
    have h1 : p * (expMin f y - expMin f x₀) ≤ p * ((y - x₀) * (c / (2 * p))) := by
      apply mul_le_mul_of_nonneg_left _ hp.le
      exact hd.trans (mul_le_mul_of_nonneg_left hT (by linarith))
    have h2 : p * ((y - x₀) * (c / (2 * p))) = c / 2 * (y - x₀) := by
      field_simp
    have hy0 : 0 < y := lt_of_le_of_lt hx₀ hy
    rw [abs_of_pos hy0]
    have h6 : min (p - c) (c / 2) * y ≤ c / 2 * y := mul_le_mul_of_nonneg_right hκ2 hy0.le
    linarith

/-! ## Nonconstancy of the profit on the decision domain -/

open BoundedNVAudit.Stakes BoundedNV.Uniform in
lemma z7_T_eq (f : ℝ → ℝ) (hf : IsGeneralDemandDensity f) (p c : ℝ) (hcp : c < p)
    (U : Set ℝ) (hU : IsOpen U)
    (hπU : ∀ z ∈ U, ∀ w ∈ U, nvProfit f p c z = nvProfit f p c w) :
    ∀ z ∈ U, ∫ t, (Set.Ioi z).indicator f t = c / p := by
  intro z hz
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z hz
  have hδ : 0 < ε / 2 := half_pos hε
  have hxU : z - ε / 2 ∈ U := hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith)]; linarith)
  have hyU : z + ε / 2 ∈ U := hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]; linarith)
  have e1 := hπU _ hyU z hz
  have e2 := hπU z hz _ hxU
  unfold nvProfit at e1 e2
  have u1 := z7_m_diff_le f hf (show z ≤ z + ε / 2 by linarith)
  have l2 := z7_m_diff_ge f hf (show z - ε / 2 ≤ z by linarith)
  rw [show z + ε / 2 - z = ε / 2 by ring] at u1
  rw [show z - (z - ε / 2) = ε / 2 by ring] at l2
  have hp : p ≠ 0 := by
    intro hp0
    have hc0 : c * (ε / 2) = 0 := by rw [hp0] at e1; linarith
    rcases mul_eq_zero.mp hc0 with h | h
    · linarith
    · linarith
  have hD : expMin f (z + ε / 2) - expMin f z = expMin f z - expMin f (z - ε / 2) := by
    apply mul_left_cancel₀ hp
    linarith
  have hDT : expMin f (z + ε / 2) - expMin f z = ε / 2 * ∫ t, (Set.Ioi z).indicator f t := by
    linarith
  have hmul : p * (ε / 2 * ∫ t, (Set.Ioi z).indicator f t) = c * (ε / 2) := by
    rw [← hDT]; linarith
  rw [eq_div_iff hp]
  have := mul_left_cancel₀ hδ.ne'
    (show ε / 2 * ((∫ t, (Set.Ioi z).indicator f t) * p) = ε / 2 * c by linarith)
  exact this

open BoundedNVAudit.Stakes BoundedNV.Uniform in
lemma z7_nonconst (f : ℝ → ℝ) (hf : IsGeneralDemandDensity f) (p c : ℝ) (hcp : c < p) :
    ¬ ∃ a : ℝ, nvProfit f p c =ᵐ[volume.restrict (BoundedNV.ExpFam.decisionDomain f)]
      (fun _ => a) := by
  rintro ⟨a, ha⟩
  have hS := z7_S_meas f
  have hcont := z7_cont f hf p c
  have hA : ∀ z ∈ interior (BoundedNV.ExpFam.decisionDomain f), nvProfit f p c z = a := by
    intro z hz
    by_contra hne
    have hV : IsOpen (interior (BoundedNV.ExpFam.decisionDomain f) ∩
        {y | nvProfit f p c y ≠ a}) :=
      isOpen_interior.inter (isOpen_ne_fun hcont continuous_const)
    have hpos := hV.measure_pos volume ⟨z, hz, hne⟩
    have h0 : volume.restrict (BoundedNV.ExpFam.decisionDomain f)
        {y | nvProfit f p c y ≠ a} = 0 := ae_iff.mp ha
    rw [Measure.restrict_apply' hS] at h0
    have hle : volume (interior (BoundedNV.ExpFam.decisionDomain f) ∩
        {y | nvProfit f p c y ≠ a}) ≤
        volume ({y | nvProfit f p c y ≠ a} ∩ BoundedNV.ExpFam.decisionDomain f) :=
      measure_mono (fun y hy => ⟨hy.2, interior_subset hy.1⟩)
    rw [h0] at hle
    exact absurd (le_antisymm hle (zero_le)) hpos.ne'
  have hT := z7_T_eq f hf p c hcp _ isOpen_interior
    (fun z hz w hw => (hA z hz).trans (hA w hw).symm)
  have hTi : ∀ w, ∫ t, (Set.Ioi w).indicator f t = ∫ t in Set.Ioi w, f t :=
    fun w => integral_indicator measurableSet_Ioi
  have hsplit : ∀ x y : ℝ, x ≤ y →
      ∫ t in Set.Ioi x, f t = (∫ t in Set.Ioc x y, f t) + ∫ t in Set.Ioi y, f t := by
    intro x y hxy
    have hu := setIntegral_union (μ := volume) (f := f) (s := Set.Ioc x y) (t := Set.Ioi y)
      (Set.disjoint_left.mpr fun t (h1 : t ∈ Set.Ioc x y) (h2 : t ∈ Set.Ioi y) =>
        absurd (show y < t from h2) (not_lt.mpr h1.2)) measurableSet_Ioi
      hf.integrable.integrableOn hf.integrable.integrableOn
    rw [← Set.Ioc_union_Ioi_eq_Ioi hxy]
    exact hu
  set ν : Measure ℝ := volume.withDensity (fun d => ENNReal.ofReal (f d)) with hν
  have hνset : ∀ s : Set ℝ, MeasurableSet s → ν s = ENNReal.ofReal (∫ t in s, f t) := by
    intro s hs
    rw [hν, withDensity_apply _ hs,
      ← ofReal_integral_eq_lintegral_ofReal hf.integrable.integrableOn (ae_of_all _ hf.nonneg)]
  have hnull : ν (interior (BoundedNV.ExpFam.decisionDomain f)) = 0 := by
    refine measure_null_of_locally_null _ (fun z hz => ?_)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
    have hxU : z - ε / 2 ∈ interior (BoundedNV.ExpFam.decisionDomain f) := hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith)]; linarith)
    have hyU : z + ε / 2 ∈ interior (BoundedNV.ExpFam.decisionDomain f) := hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]; linarith)
    refine ⟨Set.Ioo (z - ε / 2) (z + ε / 2),
      mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)), ?_⟩
    refine measure_mono_null Set.Ioo_subset_Ioc_self ?_
    rw [hνset _ measurableSet_Ioc]
    have h1 := hT _ hxU
    have h2 := hT _ hyU
    rw [hTi] at h1 h2
    have h3 := hsplit (z - ε / 2) (z + ε / 2) (by linarith)
    have h4 : ∫ t in Set.Ioc (z - ε / 2) (z + ε / 2), f t = 0 :=
      add_right_cancel ((h3.symm.trans (h1.trans h2.symm)).trans (zero_add _).symm)
    rw [h4, ENNReal.ofReal_zero]
  have hfr : interior (BoundedNV.ExpFam.decisionDomain f) =ᵐ[volume]
      BoundedNV.ExpFam.decisionDomain f :=
    interior_ae_eq_of_null_frontier
      ((convex_convexHull ℝ (Function.support f)).addHaar_frontier volume)
  have hone : ν (interior (BoundedNV.ExpFam.decisionDomain f)) = 1 := by
    rw [hνset _ isOpen_interior.measurableSet, setIntegral_congr_set hfr,
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => z7_f_off f x hx),
      hf.mass_one, ENNReal.ofReal_one]
  rw [hnull] at hone
  exact zero_ne_one hone

/-! ## Generic logit-law lemmas -/

lemma z7_vol (S : Set ℝ) (u : ℝ → ℝ) (β : ℝ)
    (hN : BoundedNVAudit.Stakes.LogitNormalizable S u β) : 0 < volume S := by
  rw [pos_iff_ne_zero]
  intro h0
  have h := hN.2
  rw [Measure.restrict_eq_zero.mpr h0, integral_zero_measure] at h
  exact lt_irrefl _ h

open BoundedNVAudit.Stakes BoundedNV.Uniform in
lemma z7_dens_nonneg (S : Set ℝ) (u : ℝ → ℝ) (β y : ℝ) : 0 ≤ logitDensity S u β y := by
  unfold logitDensity
  apply Set.indicator_nonneg
  intro y _
  exact div_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => (Real.exp_pos _).le)

open BoundedNVAudit.Stakes BoundedNV.Uniform in
lemma z7_dens_meas (S : Set ℝ) (hS : MeasurableSet S) (u : ℝ → ℝ) (hu : Measurable u) (β : ℝ) :
    Measurable (fun y => logitDensity S u β y) := by
  have e : (fun y => logitDensity S u β y) =
      S.indicator (fun y => Real.exp (u y / β) / ∫ v in S, Real.exp (u v / β)) := rfl
  rw [e]
  exact ((Real.measurable_exp.comp (hu.div_const β)).div_const _).indicator hS

open BoundedNVAudit.Stakes BoundedNV.Uniform in
lemma z7_prob (S : Set ℝ) (hS : MeasurableSet S) (u : ℝ → ℝ) (hu : Measurable u) (β : ℝ)
    (hN : LogitNormalizable S u β) : IsProbabilityMeasure (logitMeasure S u β) := by
  have hint : Integrable (fun y => logitDensity S u β y) := by
    have h := hN.1.div_const (∫ v in S, Real.exp (u v / β))
    exact IntegrableOn.integrable_indicator h hS
  have hone : ∫ y, logitDensity S u β y = 1 := by
    show ∫ y, S.indicator (fun y => Real.exp (u y / β) / ∫ v in S, Real.exp (u v / β)) y = 1
    rw [integral_indicator hS, integral_div, div_self hN.2.ne']
  constructor
  unfold logitMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (z7_dens_nonneg S u β)), hone,
    ENNReal.ofReal_one]

open BoundedNVAudit.Stakes BoundedNV.Uniform in
lemma z7_int_iff (S : Set ℝ) (hS : MeasurableSet S) (u : ℝ → ℝ) (hu : Measurable u) (β : ℝ)
    (g : ℝ → ℝ) :
    Integrable g (logitMeasure S u β) ↔ Integrable (fun x => g x * logitDensity S u β x) := by
  unfold logitMeasure
  rw [integrable_withDensity_iff_integrable_smul' (z7_dens_meas S hS u hu β).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have e : (fun x => (ENNReal.ofReal (logitDensity S u β x)).toReal • g x) =
      fun x => g x * logitDensity S u β x := by
    funext x
    rw [ENNReal.toReal_ofReal (z7_dens_nonneg S u β x), smul_eq_mul, mul_comm]
  rw [e]

open BoundedNVAudit.Stakes BoundedNV.Uniform in
lemma z7_integral (S : Set ℝ) (hS : MeasurableSet S) (u : ℝ → ℝ) (hu : Measurable u) (β : ℝ)
    (g : ℝ → ℝ) : ∫ x, g x ∂(logitMeasure S u β) = logitExp S u β g := by
  unfold logitMeasure logitExp
  rw [integral_withDensity_eq_integral_toReal_smul (z7_dens_meas S hS u hu β).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext x
  rw [ENNReal.toReal_ofReal (z7_dens_nonneg S u β x), smul_eq_mul, mul_comm]

open BoundedNVAudit.Stakes BoundedNV.Uniform in
lemma z7_lint (S : Set ℝ) (hS : MeasurableSet S) (u : ℝ → ℝ) (hu : Measurable u) (β : ℝ)
    (g : ℝ → ℝ) (hg : Measurable g) :
    ∫⁻ x, ENNReal.ofReal (g x) ∂(logitMeasure S u β) =
      ∫⁻ x, ENNReal.ofReal (g x * logitDensity S u β x) := by
  unfold logitMeasure
  rw [lintegral_withDensity_eq_lintegral_mul₀
    (z7_dens_meas S hS u hu β).ennreal_ofReal.aemeasurable hg.ennreal_ofReal.aemeasurable]
  congr 1
  funext x
  simp only [Pi.mul_apply]
  rw [mul_comm (g x), ENNReal.ofReal_mul (z7_dens_nonneg S u β x)]

lemma z7_ofReal_max (t d : ℝ) (hd : 0 ≤ d) :
    ENNReal.ofReal (t * d) = ENNReal.ofReal (max t 0 * d) := by
  rcases le_total 0 t with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, zero_mul, ENNReal.ofReal_zero, ENNReal.ofReal_eq_zero]
    nlinarith

lemma z7_ext_eq {μ : Measure ℝ} (g : ℝ → ℝ) (hg : Integrable g μ) :
    extendedExpectation μ g = ((∫ x, g x ∂μ : ℝ) : EReal) := by
  unfold extendedExpectation
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg]
  have h1 : ∫⁻ x, ENNReal.ofReal (g x) ∂μ < ⊤ := hg.lintegral_lt_top
  have h2 : ∫⁻ x, ENNReal.ofReal (-g x) ∂μ < ⊤ := hg.neg.lintegral_lt_top
  rw [← EReal.coe_ennreal_toReal h1.ne, ← EReal.coe_ennreal_toReal h2.ne, ← EReal.coe_sub]

lemma z7_int_of_fin {μ : Measure ℝ} (g : ℝ → ℝ) (hg : Measurable g)
    (h1 : ∫⁻ x, ENNReal.ofReal (g x) ∂μ < ⊤) (h2 : ∫⁻ x, ENNReal.ofReal (-g x) ∂μ < ⊤) :
    Integrable g μ := by
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  show ∫⁻ x, ‖g x‖ₑ ∂μ < ⊤
  calc ∫⁻ x, ‖g x‖ₑ ∂μ ≤ ∫⁻ x, (ENNReal.ofReal (g x) + ENNReal.ofReal (-g x)) ∂μ := by
        refine lintegral_mono (fun x => ?_)
        rw [Real.enorm_eq_ofReal_abs]
        rcases le_total 0 (g x) with h | h
        · rw [abs_of_nonneg h]; exact le_self_add
        · rw [abs_of_nonpos h]; exact le_add_self
    _ = ∫⁻ x, ENNReal.ofReal (g x) ∂μ + ∫⁻ x, ENNReal.ofReal (-g x) ∂μ :=
        lintegral_add_left hg.ennreal_ofReal _
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨h1, h2⟩

lemma z7_E_lt (A₁ B₁ A₂ B₂ : ENNReal) (hA₂ : A₂ < ⊤) (hB₁ : B₁ < ⊤)
    (h : A₁ < ⊤ → B₂ < ⊤ → A₂.toReal - B₂.toReal < A₁.toReal - B₁.toReal) :
    (A₂ : EReal) - B₂ < (A₁ : EReal) - B₁ := by
  rw [← EReal.coe_ennreal_toReal hB₁.ne, ← EReal.coe_ennreal_toReal hA₂.ne]
  rcases eq_or_ne B₂ ⊤ with hB₂ | hB₂ <;> rcases eq_or_ne A₁ ⊤ with hA₁ | hA₁
  · rw [hB₂, hA₁, EReal.coe_ennreal_top, EReal.sub_top, EReal.top_sub_coe]
    exact bot_lt_top
  · rw [hB₂, EReal.coe_ennreal_top, EReal.sub_top, ← EReal.coe_ennreal_toReal hA₁,
      ← EReal.coe_sub]
    exact EReal.bot_lt_coe _
  · rw [hA₁, EReal.coe_ennreal_top, EReal.top_sub_coe, ← EReal.coe_ennreal_toReal hB₂,
      ← EReal.coe_sub]
    exact EReal.coe_lt_top _
  · rw [← EReal.coe_ennreal_toReal hA₁, ← EReal.coe_ennreal_toReal hB₂, ← EReal.coe_sub,
      ← EReal.coe_sub, EReal.coe_lt_coe_iff]
    exact h (lt_top_iff_ne_top.mpr hA₁) (lt_top_iff_ne_top.mpr hB₂)

open BoundedNVAudit.Stakes BoundedNV.Uniform in
lemma z7_logitExp_eq (S : Set ℝ) (hS : MeasurableSet S) (u g : ℝ → ℝ) (β : ℝ) :
    logitExp S u β g =
      (∫ y in S, g y * Real.exp (u y / β)) / ∫ v in S, Real.exp (u v / β) := by
  unfold logitExp logitDensity
  have : (fun y => g y * S.indicator
      (fun y => Real.exp (u y / β) / ∫ v in S, Real.exp (u v / β)) y) =
      S.indicator (fun y => g y * Real.exp (u y / β) / ∫ v in S, Real.exp (u v / β)) := by
    funext y
    by_cases hy : y ∈ S <;> simp [hy, mul_div_assoc]
  rw [this, integral_indicator hS, integral_div]

/-! ## Exponential tilting -/

lemma z7_hrel (φ β a b : ℝ) (hβ : 0 < β) :
    Real.exp (b * φ / β) = Real.exp ((b - a) / β * φ) * Real.exp (a * φ / β) := by
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

open BoundedNVAudit.Stakes BoundedNV.Uniform in
lemma z7_GA (S : Set ℝ) (hS : MeasurableSet S) (φ : ℝ → ℝ) (hφ : Measurable φ)
    (β a b : ℝ) (hβ : 0 < β) (hab : a < b)
    (hNa : LogitNormalizable S (fun x => a * φ x) β)
    (hNb : LogitNormalizable S (fun x => b * φ x) β) :
    Integrable (fun x => max (φ x) 0 * logitDensity S (fun y => a * φ y) β x) := by
  have hk : 0 < (b - a) / β := div_pos (sub_pos.mpr hab) hβ
  have hZa : 0 < ∫ v in S, Real.exp (a * φ v / β) := hNa.2
  have hdom : Integrable (fun x => 1 / ((b - a) / β * ∫ v in S, Real.exp (a * φ v / β)) *
      S.indicator (fun y => Real.exp (b * φ y / β)) x) :=
    (hNb.1.integrable_indicator hS).const_mul _
  refine Integrable.mono' hdom
    ((hφ.max measurable_const).mul (z7_dens_meas S hS _ (measurable_const.mul hφ) β)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) (z7_dens_nonneg _ _ _ _))]
  by_cases hx : x ∈ S
  · simp only [logitDensity, Set.indicator_of_mem hx]
    rw [z7_hrel (φ x) β a b hβ]
    have h1 : max (φ x) 0 ≤ Real.exp ((b - a) / β * φ x) / ((b - a) / β) := by
      rw [le_div_iff₀ hk]
      rcases le_total 0 (φ x) with h | h
      · rw [max_eq_left h]
        nlinarith [Real.add_one_le_exp ((b - a) / β * φ x)]
      · rw [max_eq_right h, zero_mul]; exact (Real.exp_pos _).le
    calc max (φ x) 0 * (Real.exp (a * φ x / β) / ∫ v in S, Real.exp (a * φ v / β))
        ≤ Real.exp ((b - a) / β * φ x) / ((b - a) / β) *
          (Real.exp (a * φ x / β) / ∫ v in S, Real.exp (a * φ v / β)) :=
          mul_le_mul_of_nonneg_right h1 (div_nonneg (Real.exp_pos _).le hZa.le)
      _ = _ := by field_simp
  · simp only [logitDensity, Set.indicator_of_notMem hx, mul_zero, le_refl]

open BoundedNVAudit.Stakes BoundedNV.Uniform in
lemma z7_GB (S : Set ℝ) (hS : MeasurableSet S) (φ : ℝ → ℝ) (hφ : Measurable φ)
    (β a b : ℝ) (hβ : 0 < β) (hab : a < b)
    (hNa : LogitNormalizable S (fun x => a * φ x) β)
    (hNb : LogitNormalizable S (fun x => b * φ x) β) :
    Integrable (fun x => max (-φ x) 0 * logitDensity S (fun y => b * φ y) β x) := by
  have hk : 0 < (b - a) / β := div_pos (sub_pos.mpr hab) hβ
  have hZb : 0 < ∫ v in S, Real.exp (b * φ v / β) := hNb.2
  have hdom : Integrable (fun x => 1 / ((b - a) / β * ∫ v in S, Real.exp (b * φ v / β)) *
      S.indicator (fun y => Real.exp (a * φ y / β)) x) :=
    (hNa.1.integrable_indicator hS).const_mul _
  refine Integrable.mono' hdom
    ((hφ.neg.max measurable_const).mul
      (z7_dens_meas S hS _ (measurable_const.mul hφ) β)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) (z7_dens_nonneg _ _ _ _))]
  by_cases hx : x ∈ S
  · simp only [logitDensity, Set.indicator_of_mem hx]
    rw [z7_hrel (φ x) β a b hβ]
    set k := (b - a) / β with hkdef
    have h1 : max (-φ x) 0 * Real.exp (k * φ x) ≤ 1 / k := by
      rw [le_div_iff₀ hk]
      rcases le_total 0 (φ x) with h | h
      · rw [max_eq_right (by linarith), zero_mul, zero_mul]; exact zero_le_one
      · rw [max_eq_left (by linarith)]
        have e1 := Real.add_one_le_exp (-(k * φ x))
        have e2 : Real.exp (-(k * φ x)) * Real.exp (k * φ x) = 1 := by
          rw [← Real.exp_add]; simp
        have e3 := Real.exp_pos (k * φ x)
        have e4 := mul_le_mul_of_nonneg_right e1 e3.le
        rw [e2] at e4
        nlinarith
    calc max (-φ x) 0 * (Real.exp (k * φ x) * Real.exp (a * φ x / β) /
          ∫ v in S, Real.exp (b * φ v / β))
        = (max (-φ x) 0 * Real.exp (k * φ x)) *
          (Real.exp (a * φ x / β) / ∫ v in S, Real.exp (b * φ v / β)) := by ring
      _ ≤ 1 / k * (Real.exp (a * φ x / β) / ∫ v in S, Real.exp (b * φ v / β)) :=
          mul_le_mul_of_nonneg_right h1 (div_nonneg (Real.exp_pos _).le hZb.le)
      _ = _ := by field_simp
  · simp only [logitDensity, Set.indicator_of_notMem hx, mul_zero, le_refl]

open BoundedNVAudit.Stakes BoundedNV.Uniform in
lemma z7_GC (S : Set ℝ) (hS : MeasurableSet S) (φ : ℝ → ℝ)
    (β a b : ℝ) (hβ : 0 < β) (hab : a < b)
    (hNa : LogitNormalizable S (fun x => a * φ x) β)
    (hNb : LogitNormalizable S (fun x => b * φ x) β)
    (hnc : ¬ ∃ m : ℝ, φ =ᵐ[volume.restrict S] (fun _ => m))
    (hia : Integrable (fun x => φ x * logitDensity S (fun y => a * φ y) β x))
    (hib : Integrable (fun x => φ x * logitDensity S (fun y => b * φ y) β x)) :
    logitExp S (fun y => a * φ y) β φ < logitExp S (fun y => b * φ y) β φ := by
  simp only [z7_logitExp_eq S hS]
  have hk : 0 < (b - a) / β := div_pos (sub_pos.mpr hab) hβ
  have hZa : 0 < ∫ v in S, Real.exp (a * φ v / β) := hNa.2
  have hZb : 0 < ∫ v in S, Real.exp (b * φ v / β) := hNb.2
  have hIa : IntegrableOn (fun x => φ x * Real.exp (a * φ x / β)) S := by
    refine ((hia.const_mul (∫ v in S, Real.exp (a * φ v / β))).integrableOn).congr_fun
      (fun x hx => ?_) hS
    simp only [logitDensity, Set.indicator_of_mem hx]
    field_simp
  have hIb : IntegrableOn (fun x => φ x * Real.exp (b * φ x / β)) S := by
    refine ((hib.const_mul (∫ v in S, Real.exp (b * φ v / β))).integrableOn).congr_fun
      (fun x hx => ?_) hS
    simp only [logitDensity, Set.indicator_of_mem hx]
    field_simp
  set Ia := ∫ y in S, φ y * Real.exp (a * φ y / β) with hIadef
  set Za := ∫ v in S, Real.exp (a * φ v / β) with hZadef
  set Ib := ∫ y in S, φ y * Real.exp (b * φ y / β) with hIbdef
  set Zb := ∫ v in S, Real.exp (b * φ v / β) with hZbdef
  set m := Ia / Za with hmdef
  set k := (b - a) / β with hkdef
  have hFint : IntegrableOn (fun x => (φ x * Real.exp (b * φ x / β) - m * Real.exp (b * φ x / β))
      - Real.exp (k * m) * (φ x * Real.exp (a * φ x / β) - m * Real.exp (a * φ x / β))) S :=
    (hIb.sub (hNb.1.const_mul m)).sub ((hIa.sub (hNa.1.const_mul m)).const_mul _)
  have hFval : ∀ x, (φ x * Real.exp (b * φ x / β) - m * Real.exp (b * φ x / β))
      - Real.exp (k * m) * (φ x * Real.exp (a * φ x / β) - m * Real.exp (a * φ x / β)) =
      Real.exp (a * φ x / β) * ((φ x - m) * (Real.exp (k * φ x) - Real.exp (k * m))) := by
    intro x
    rw [z7_hrel (φ x) β a b hβ]
    ring
  have hFpos : ∀ x, φ x ≠ m → 0 < (φ x * Real.exp (b * φ x / β) - m * Real.exp (b * φ x / β))
      - Real.exp (k * m) * (φ x * Real.exp (a * φ x / β) - m * Real.exp (a * φ x / β)) := by
    intro x hx
    rw [hFval x]
    refine mul_pos (Real.exp_pos _) ?_
    rcases lt_or_gt_of_ne hx with h | h
    · exact mul_pos_of_neg_of_neg (sub_neg.mpr h)
        (sub_neg.mpr (Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left h hk)))
    · exact mul_pos (sub_pos.mpr h)
        (sub_pos.mpr (Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left h hk)))
  have hFnn : ∀ x, 0 ≤ (φ x * Real.exp (b * φ x / β) - m * Real.exp (b * φ x / β))
      - Real.exp (k * m) * (φ x * Real.exp (a * φ x / β) - m * Real.exp (a * φ x / β)) := by
    intro x
    by_cases hx : φ x = m
    · rw [hFval x, hx, sub_self, zero_mul, mul_zero]
    · exact (hFpos x hx).le
  have hFeq : ∫ x in S, ((φ x * Real.exp (b * φ x / β) - m * Real.exp (b * φ x / β))
      - Real.exp (k * m) * (φ x * Real.exp (a * φ x / β) - m * Real.exp (a * φ x / β))) =
      Ib - m * Zb := by
    have e1 : ∫ x in S, ((φ x * Real.exp (b * φ x / β) - m * Real.exp (b * φ x / β))
        - Real.exp (k * m) * (φ x * Real.exp (a * φ x / β) - m * Real.exp (a * φ x / β))) =
        (∫ x in S, (φ x * Real.exp (b * φ x / β) - m * Real.exp (b * φ x / β)))
        - ∫ x in S, Real.exp (k * m) * (φ x * Real.exp (a * φ x / β) - m * Real.exp (a * φ x / β)) :=
      integral_sub (hIb.sub (hNb.1.const_mul m)) ((hIa.sub (hNa.1.const_mul m)).const_mul _)
    have e2 : ∫ x in S, (φ x * Real.exp (b * φ x / β) - m * Real.exp (b * φ x / β)) =
        Ib - m * Zb := by
      rw [hIbdef, hZbdef, ← integral_const_mul]
      exact integral_sub hIb (hNb.1.const_mul m)
    have e3 : ∫ x in S, Real.exp (k * m) * (φ x * Real.exp (a * φ x / β) - m * Real.exp (a * φ x / β)) =
        Real.exp (k * m) * (Ia - m * Za) := by
      rw [integral_const_mul]
      congr 1
      rw [hIadef, hZadef, ← integral_const_mul]
      exact integral_sub hIa (hNa.1.const_mul m)
    rw [e1, e2, e3]
    have : m * Za = Ia := div_mul_cancel₀ Ia hZa.ne'
    rw [this, sub_self, mul_zero, sub_zero]
  rw [lt_div_iff₀ hZb]
  by_contra hle
  push_neg at hle
  have h0 : ∫ x in S, ((φ x * Real.exp (b * φ x / β) - m * Real.exp (b * φ x / β))
      - Real.exp (k * m) * (φ x * Real.exp (a * φ x / β) - m * Real.exp (a * φ x / β))) = 0 := by
    have hge := setIntegral_nonneg (μ := volume) hS (fun x _ => hFnn x)
    rw [hFeq] at hge ⊢
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => hFnn x) hFint).mp h0
  apply hnc
  refine ⟨m, ?_⟩
  filter_upwards [hae] with x hx
  by_contra hne
  exact (hFpos x hne).ne' hx

/-! ## Decay bound for the integrable case -/

lemma z7_pt_bound (A κ μ' t y : ℝ) (hκ : 0 < κ) (hμ : 0 < μ') (ht : t ≤ A - κ * |y|) :
    |t| * Real.exp (2 * μ' * t) ≤
      ((|A| * Real.exp (μ' * |A|) + 1 / μ') * Real.exp (μ' * A) /
        min 1 ((μ' * κ) ^ 2 / 2)) * (1 + y ^ 2)⁻¹ := by
  have hb : 0 < μ' * κ := mul_pos hμ hκ
  have hm0 : 0 < min 1 ((μ' * κ) ^ 2 / 2) := lt_min one_pos (by positivity)
  have hy2 : 0 < 1 + y ^ 2 := by positivity
  have hE : min 1 ((μ' * κ) ^ 2 / 2) * (1 + y ^ 2) ≤ Real.exp (μ' * κ * |y|) := by
    have h1 := Real.quadratic_le_exp_of_nonneg (mul_nonneg hb.le (abs_nonneg y))
    have h2 : (μ' * κ * |y|) ^ 2 = (μ' * κ) ^ 2 * y ^ 2 := by rw [mul_pow, sq_abs]
    rw [h2] at h1
    have h3 : min 1 ((μ' * κ) ^ 2 / 2) ≤ 1 := min_le_left _ _
    have h4 : min 1 ((μ' * κ) ^ 2 / 2) ≤ (μ' * κ) ^ 2 / 2 := min_le_right _ _
    have h5 : min 1 ((μ' * κ) ^ 2 / 2) * y ^ 2 ≤ (μ' * κ) ^ 2 / 2 * y ^ 2 :=
      mul_le_mul_of_nonneg_right h4 (sq_nonneg y)
    have h6 : 0 ≤ μ' * κ * |y| := mul_nonneg hb.le (abs_nonneg y)
    nlinarith
  have hK0 : 0 ≤ |A| * Real.exp (μ' * |A|) := mul_nonneg (abs_nonneg A) (Real.exp_pos _).le
  have hinv : 0 < 1 / μ' := by positivity
  have htA : t ≤ A := by nlinarith [abs_nonneg y]
  have hK : |t| * Real.exp (μ' * t) ≤ |A| * Real.exp (μ' * |A|) + 1 / μ' := by
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h]
      have : t * Real.exp (μ' * t) ≤ |A| * Real.exp (μ' * |A|) :=
        mul_le_mul (htA.trans (le_abs_self A))
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (htA.trans (le_abs_self A)) hμ.le))
          (Real.exp_pos _).le (abs_nonneg A)
      linarith
    · rw [abs_of_nonpos h]
      have e1 := Real.add_one_le_exp (-(μ' * t))
      have e2 : Real.exp (-(μ' * t)) * Real.exp (μ' * t) = 1 := by
        rw [← Real.exp_add]; simp
      have e3 := Real.exp_pos (μ' * t)
      have e4 := mul_le_mul_of_nonneg_right e1 e3.le
      rw [e2] at e4
      have e5 : -t * Real.exp (μ' * t) ≤ 1 / μ' := by
        rw [le_div_iff₀ hμ]; nlinarith
      linarith
  have hT : Real.exp (μ' * t) * Real.exp (μ' * κ * |y|) ≤ Real.exp (μ' * A) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left ht hμ.le]
  have e2 : Real.exp (2 * μ' * t) = Real.exp (μ' * t) * Real.exp (μ' * t) := by
    rw [← Real.exp_add]; ring_nf
  rw [e2]
  have hEt := Real.exp_pos (μ' * t)
  have hF := Real.exp_pos (μ' * κ * |y|)
  have p1 : |t| * Real.exp (μ' * t) * Real.exp (μ' * t) *
      (min 1 ((μ' * κ) ^ 2 / 2) * (1 + y ^ 2)) ≤
      |t| * Real.exp (μ' * t) * Real.exp (μ' * t) * Real.exp (μ' * κ * |y|) :=
    mul_le_mul_of_nonneg_left hE (by positivity)
  have p2 : |t| * Real.exp (μ' * t) * (Real.exp (μ' * t) * Real.exp (μ' * κ * |y|)) ≤
      (|A| * Real.exp (μ' * |A|) + 1 / μ') * (Real.exp (μ' * t) * Real.exp (μ' * κ * |y|)) :=
    mul_le_mul_of_nonneg_right hK (by positivity)
  have p3 : (|A| * Real.exp (μ' * |A|) + 1 / μ') * (Real.exp (μ' * t) * Real.exp (μ' * κ * |y|))
      ≤ (|A| * Real.exp (μ' * |A|) + 1 / μ') * Real.exp (μ' * A) :=
    mul_le_mul_of_nonneg_left hT (by positivity)
  calc |t| * (Real.exp (μ' * t) * Real.exp (μ' * t))
      ≤ (|A| * Real.exp (μ' * |A|) + 1 / μ') * Real.exp (μ' * A) /
          (min 1 ((μ' * κ) ^ 2 / 2) * (1 + y ^ 2)) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
    _ = _ := by field_simp

open BoundedNVAudit.Stakes BoundedNV.Uniform in
lemma z7_GD (S : Set ℝ) (hS : MeasurableSet S) (φ : ℝ → ℝ) (hφ : Measurable φ)
    (A κ lam β : ℝ) (hκ : 0 < κ) (hlam : 0 < lam) (hβ : 0 < β)
    (hb : ∀ y, φ y ≤ A - κ * |y|) (hN : LogitNormalizable S (fun x => lam * φ x) β) :
    Integrable (fun x => φ x * logitDensity S (fun y => lam * φ y) β x) := by
  have hμ : 0 < lam / (2 * β) := by positivity
  have hZ : 0 < ∫ v in S, Real.exp (lam * φ v / β) := hN.2
  set C := (|A| * Real.exp (lam / (2 * β) * |A|) + 1 / (lam / (2 * β))) *
      Real.exp (lam / (2 * β) * A) / min 1 ((lam / (2 * β) * κ) ^ 2 / 2) with hC
  have hdom : Integrable (fun x : ℝ => C / (∫ v in S, Real.exp (lam * φ v / β)) *
      (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul _
  refine Integrable.mono' hdom
    (hφ.mul (z7_dens_meas S hS _ (measurable_const.mul hφ) β)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (z7_dens_nonneg _ _ _ _)]
  by_cases hx : x ∈ S
  · simp only [logitDensity, Set.indicator_of_mem hx]
    have hpt := z7_pt_bound A κ (lam / (2 * β)) (φ x) x hκ hμ (hb x)
    have e : lam * φ x / β = 2 * (lam / (2 * β)) * φ x := by field_simp
    rw [e]
    calc |φ x| * (Real.exp (2 * (lam / (2 * β)) * φ x) / ∫ v in S, Real.exp (lam * φ v / β))
        = (|φ x| * Real.exp (2 * (lam / (2 * β)) * φ x)) /
          ∫ v in S, Real.exp (lam * φ v / β) := by ring
      _ ≤ (C * (1 + x ^ 2)⁻¹) / ∫ v in S, Real.exp (lam * φ v / β) :=
          (div_le_div_iff_of_pos_right hZ).mpr hpt
      _ = _ := by ring
  · simp only [logitDensity, Set.indicator_of_notMem hx, abs_zero, mul_zero]
    have : 0 ≤ C := by
      rw [hC]
      have : 0 < min 1 ((lam / (2 * β) * κ) ^ 2 / 2) :=
        lt_min one_pos (by positivity)
      positivity
    positivity

/-! ## Main theorem -/

open MeasureTheory BoundedNVAudit.Stakes QAlgorithms.Papers.Independent.Next46.P01 in
theorem solution
    (f : ℝ → ℝ) (hf : IsGeneralDemandDensity f)
    (p c β lam₁ lam₂ : ℝ) (hcp : c < p) (hβ : 0 < β) (hlam : lam₂ < lam₁)
    (h₁ : LogitNormalizable (BoundedNV.ExpFam.decisionDomain f)
      (fun x => lam₁ * BoundedNV.Uniform.nvProfit f p c x) β)
    (h₂ : LogitNormalizable (BoundedNV.ExpFam.decisionDomain f)
      (fun x => lam₂ * BoundedNV.Uniform.nvProfit f p c x) β) :
    let S := BoundedNV.ExpFam.decisionDomain f
    let π := BoundedNV.Uniform.nvProfit f p c
    let μ₁ := logitMeasure S (fun x => lam₁ * π x) β
    let μ₂ := logitMeasure S (fun x => lam₂ * π x) β
    (∀ x : ℝ, Integrable (fun d => min d x * f d)) ∧
    MeasurableSet S ∧ 0 < volume S ∧ Continuous π ∧
    (¬ ∃ a : ℝ, π =ᵐ[volume.restrict S] (fun _ => a)) ∧
    IsProbabilityMeasure μ₁ ∧ IsProbabilityMeasure μ₂ ∧
    (∫⁻ x, ENNReal.ofReal (π x) ∂μ₂) < ⊤ ∧
    (∫⁻ x, ENNReal.ofReal (-π x) ∂μ₁) < ⊤ ∧
    extendedExpectation μ₂ π < extendedExpectation μ₁ π ∧
    (0 < c → 0 < lam₂ → Integrable π μ₁ ∧ Integrable π μ₂) ∧
    (∀ lam ∈ ({lam₁, lam₂} : Set ℝ),
      let μ := logitMeasure S (fun x => lam * π x) β
      Integrable π μ ↔ Integrable (fun x => π x *
        BoundedNV.Uniform.logitDensity S (fun y => lam * π y) β x)) ∧
    (∀ lam ∈ ({lam₁, lam₂} : Set ℝ),
      let μ := logitMeasure S (fun x => lam * π x) β
      Integrable π μ →
        extendedExpectation μ π = ((∫ x, π x ∂μ : ℝ) : EReal) ∧
        (∫ x, π x ∂μ) = BoundedNV.Uniform.logitExp S (fun x => lam * π x) β π) ∧
    (Integrable π μ₁ → Integrable π μ₂ →
      BoundedNV.Uniform.logitExp S (fun x => lam₂ * π x) β π <
        BoundedNV.Uniform.logitExp S (fun x => lam₁ * π x) β π) := by
  intro S π μ₁ μ₂
  have hS : MeasurableSet S := z7_S_meas f
  have hπc : Continuous π := z7_cont f hf p c
  have hπm : Measurable π := hπc.measurable
  have hu : ∀ lam : ℝ, Measurable (fun x => lam * π x) := fun lam => measurable_const.mul hπm
  have hnc : ¬ ∃ a : ℝ, π =ᵐ[volume.restrict S] (fun _ => a) := z7_nonconst f hf p c hcp
  have hint : ∀ lam : ℝ, Integrable π (logitMeasure S (fun x => lam * π x) β) ↔
      Integrable (fun x => π x * BoundedNV.Uniform.logitDensity S (fun y => lam * π y) β x) :=
    fun lam => z7_int_iff S hS _ (hu lam) β π
  have hP2 : (∫⁻ x, ENNReal.ofReal (π x) ∂μ₂) < ⊤ := by
    calc (∫⁻ x, ENNReal.ofReal (π x) ∂μ₂)
        = ∫⁻ x, ENNReal.ofReal (π x *
            BoundedNV.Uniform.logitDensity S (fun y => lam₂ * π y) β x) :=
          z7_lint S hS _ (hu lam₂) β π hπm
      _ = ∫⁻ x, ENNReal.ofReal (max (π x) 0 *
            BoundedNV.Uniform.logitDensity S (fun y => lam₂ * π y) β x) :=
          lintegral_congr (fun x => z7_ofReal_max _ _ (z7_dens_nonneg _ _ _ _))
      _ < ⊤ := (z7_GA S hS π hπm β lam₂ lam₁ hβ hlam h₂ h₁).lintegral_lt_top
  have hN1 : (∫⁻ x, ENNReal.ofReal (-π x) ∂μ₁) < ⊤ := by
    calc (∫⁻ x, ENNReal.ofReal (-π x) ∂μ₁)
        = ∫⁻ x, ENNReal.ofReal (-π x *
            BoundedNV.Uniform.logitDensity S (fun y => lam₁ * π y) β x) :=
          z7_lint S hS _ (hu lam₁) β (fun x => -π x) hπm.neg
      _ = ∫⁻ x, ENNReal.ofReal (max (-π x) 0 *
            BoundedNV.Uniform.logitDensity S (fun y => lam₁ * π y) β x) :=
          lintegral_congr (fun x => z7_ofReal_max _ _ (z7_dens_nonneg _ _ _ _))
      _ < ⊤ := (z7_GB S hS π hπm β lam₂ lam₁ hβ hlam h₂ h₁).lintegral_lt_top
  have hlast : Integrable π μ₁ → Integrable π μ₂ →
      BoundedNV.Uniform.logitExp S (fun x => lam₂ * π x) β π <
        BoundedNV.Uniform.logitExp S (fun x => lam₁ * π x) β π := fun h1 h2 =>
    z7_GC S hS π β lam₂ lam₁ hβ hlam h₂ h₁ hnc ((hint lam₂).mp h2) ((hint lam₁).mp h1)
  have hE : extendedExpectation μ₂ π < extendedExpectation μ₁ π := by
    unfold extendedExpectation
    apply z7_E_lt _ _ _ _ hP2 hN1
    intro hP1 hN2
    have hi1 : Integrable π μ₁ := z7_int_of_fin π hπm hP1 hN1
    have hi2 : Integrable π μ₂ := z7_int_of_fin π hπm hP2 hN2
    have e1 : ∫ x, π x ∂μ₁ = (∫⁻ x, ENNReal.ofReal (π x) ∂μ₁).toReal -
        (∫⁻ x, ENNReal.ofReal (-π x) ∂μ₁).toReal :=
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi1
    have e2 : ∫ x, π x ∂μ₂ = (∫⁻ x, ENNReal.ofReal (π x) ∂μ₂).toReal -
        (∫⁻ x, ENNReal.ofReal (-π x) ∂μ₂).toReal :=
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi2
    have e1' : ∫ x, π x ∂μ₁ = BoundedNV.Uniform.logitExp S (fun x => lam₁ * π x) β π :=
      z7_integral S hS _ (hu lam₁) β π
    have e2' : ∫ x, π x ∂μ₂ = BoundedNV.Uniform.logitExp S (fun x => lam₂ * π x) β π :=
      z7_integral S hS _ (hu lam₂) β π
    have := hlast hi1 hi2
    linarith
  refine ⟨fun x => z7_minf_int f hf x, hS, z7_vol S _ β h₁, hπc, hnc,
    z7_prob S hS _ (hu lam₁) β h₁, z7_prob S hS _ (hu lam₂) β h₂, hP2, hN1, hE, ?_,
    fun lam _ => hint lam,
    fun lam _ h => ⟨z7_ext_eq π h, z7_integral S hS _ (hu lam) β π⟩, hlast⟩
  intro hc0 hl2
  obtain ⟨A, κ, hκ, hb⟩ := z7_upper f hf p c hc0 hcp
  have hl1 : 0 < lam₁ := hl2.trans hlam
  exact ⟨(hint lam₁).mpr (z7_GD S hS π hπm A κ lam₁ β hκ hl1 hβ hb h₁),
    (hint lam₂).mpr (z7_GD S hS π hπm A κ lam₂ β hκ hl2 hβ hb h₂)⟩

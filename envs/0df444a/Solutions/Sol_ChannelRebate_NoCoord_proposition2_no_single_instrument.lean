-- Prove2me | solution 1 for ChannelRebate.NoCoord.proposition2_no_single_instrument
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T21:51:22.6065+00:00
-- url     : https://prove2.me/submissions/7274e20d-cda7-4f60-b0fa-a60ec6d557ae

import Mathlib
import Definitions.Def_ChannelRebate_NoCoord_Setting

open MeasureTheory ProbabilityTheory

namespace RebP2

open ChannelRebate.NoCoord

lemma phi_nonneg (D : Demand) (x : ℝ) : 0 ≤ D.φ x := by
  rcases lt_or_ge x 0 with h | h
  · rw [D.φ_neg x h]
  · exact (D.φ_pos x h).le

instance law_prob (D : Demand) : IsProbabilityMeasure D.law := by
  constructor
  rw [Demand.law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal D.integrable_φ (ae_of_all _ (phi_nonneg D)),
    D.integral_φ, ENNReal.ofReal_one]

lemma meas_mul (e : ℝ) : Measurable (fun x : ℝ => e * x) := by fun_prop

instance effLaw_prob (D : Demand) (e : ℝ) : IsProbabilityMeasure (D.effLaw e) := by
  unfold Demand.effLaw
  exact Measure.isProbabilityMeasure_map (meas_mul e).aemeasurable

lemma law_meas_phi (D : Demand) : AEMeasurable (fun ξ => ENNReal.ofReal (D.φ ξ)) volume :=
  (ENNReal.measurable_ofReal.comp D.measurable_φ).aemeasurable

lemma effLaw_singleton (D : Demand) {e : ℝ} (he : 0 < e) (x : ℝ) : D.effLaw e {x} = 0 := by
  unfold Demand.effLaw
  rw [Measure.map_apply (meas_mul e) (measurableSet_singleton x)]
  apply withDensity_absolutelyContinuous
  apply Set.Subsingleton.measure_zero
  exact Set.Subsingleton.preimage Set.subsingleton_singleton (mul_right_injective₀ he.ne')

lemma effLaw_Iio (D : Demand) {e : ℝ} (he : 0 < e) : D.effLaw e (Set.Iio 0) = 0 := by
  unfold Demand.effLaw
  rw [Measure.map_apply (meas_mul e) measurableSet_Iio, Demand.law,
    withDensity_apply_eq_zero' (law_meas_phi D)]
  convert measure_empty (μ := (volume : Measure ℝ))
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iio,
    Set.mem_empty_iff_false, iff_false, not_and]
  intro h1 h2
  have : x < 0 := by
    by_contra hx; push Not at hx; nlinarith
  exact h1 (by rw [D.φ_neg x this, ENNReal.ofReal_zero])

lemma effLaw_Ioo (D : Demand) {e : ℝ} (he : 0 < e) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    0 < D.effLaw e (Set.Ioo a b) := by
  unfold Demand.effLaw
  rw [Measure.map_apply (meas_mul e) measurableSet_Ioo, Demand.law, pos_iff_ne_zero,
    Ne, withDensity_apply_eq_zero' (law_meas_phi D)]
  intro h
  have hsub : Set.Ioo (a / e) (b / e) ⊆
      {x | ENNReal.ofReal (D.φ x) ≠ 0} ∩ (fun x => e * x) ⁻¹' Set.Ioo a b := by
    intro x hx
    simp only [Set.mem_Ioo] at hx
    have h1 : a < e * x := by rw [div_lt_iff₀ he] at hx; linarith [hx.1]
    have h2 : e * x < b := by rw [lt_div_iff₀ he] at hx; linarith [hx.2]
    refine ⟨?_, ⟨h1, h2⟩⟩
    simp only [Set.mem_ofPred_eq, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    apply D.φ_pos
    have : 0 ≤ a / e := div_nonneg ha he.le
    linarith [hx.1]
  have := measure_mono_null hsub h
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at this
  have : a / e < b / e := div_lt_div_of_pos_right hab he
  linarith

lemma law_integrable_id (D : Demand) : Integrable (fun x : ℝ => x) D.law := by
  unfold Demand.law
  rw [integrable_withDensity_iff_integrable_smul₀' (law_meas_phi D)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  refine D.integrable_mul_φ.congr (ae_of_all _ (fun x => ?_))
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (phi_nonneg D x)]
  ring

lemma effLaw_integrable_id (D : Demand) (e : ℝ) : Integrable (fun x : ℝ => x) (D.effLaw e) := by
  unfold Demand.effLaw
  rw [integrable_map_measure (by fun_prop) (meas_mul e).aemeasurable]
  exact (law_integrable_id D).const_mul e

lemma effLaw_mul (D : Demand) (e t : ℝ) : D.effLaw (t * e) = (D.effLaw e).map (fun y => t * y) := by
  unfold Demand.effLaw
  rw [Measure.map_map (meas_mul t) (meas_mul e)]
  congr 1
  ext x; simp [Function.comp]; ring


section General

variable (ν : Measure ℝ) [IsProbabilityMeasure ν]

lemma int_min (hint : Integrable (fun x : ℝ => x) ν) (Q : ℝ) :
    Integrable (fun y => min Q y) ν := by
  refine Integrable.mono' ((integrable_const |Q|).add hint.abs) (by fun_prop)
    (ae_of_all _ (fun y => ?_))
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [abs_le]
  constructor
  · rcases min_choice Q y with h | h <;> rw [h] <;>
      linarith [neg_abs_le Q, neg_abs_le y, abs_nonneg Q, abs_nonneg y]
  · linarith [min_le_left Q y, le_abs_self Q, abs_nonneg y]

lemma int_reb (hint : Integrable (fun x : ℝ => x) ν) (Q T : ℝ) :
    Integrable (fun y => max (min Q y - T) 0) ν := by
  refine Integrable.mono' ((int_min ν hint Q).abs.add (integrable_const |T|)) (by fun_prop)
    (ae_of_all _ (fun y => ?_))
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [abs_of_nonneg (le_max_right _ _)]
  apply max_le
  · linarith [le_abs_self (min Q y), neg_abs_le T]
  · positivity

lemma int_ind (hint : Integrable (fun x : ℝ => x) ν) (Q T : ℝ) :
    Integrable (Set.indicator {y | T < min Q y} (fun y => min Q y)) ν :=
  (int_min ν hint Q).indicator (measurableSet_lt (by fun_prop) (by fun_prop))

lemma leftover_eq (hint : Integrable (fun x : ℝ => x) ν) (Q : ℝ) :
    CachonCoord.Newsvendor.expLeftover ν Q = Q - CachonCoord.Newsvendor.expSales ν Q := by
  unfold CachonCoord.Newsvendor.expLeftover CachonCoord.Newsvendor.expSales
  have : (fun y => max (Q - y) 0) = fun y => Q - min Q y := by
    ext y; rcases le_total Q y with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]
  rw [this, integral_sub (integrable_const Q) (int_min ν hint Q), integral_const]
  simp

lemma sales_inc (hint : Integrable (fun x : ℝ => x) ν) (Q h : ℝ) (hh : 0 ≤ h) :
    h * ν.real (Set.Ioi (Q + h)) ≤
      CachonCoord.Newsvendor.expSales ν (Q + h) - CachonCoord.Newsvendor.expSales ν Q := by
  unfold CachonCoord.Newsvendor.expSales
  rw [← integral_sub (int_min ν hint _) (int_min ν hint _), mul_comm,
    ← smul_eq_mul, ← integral_indicator_const _ measurableSet_Ioi]
  refine integral_mono ((integrable_const h).indicator measurableSet_Ioi)
    ((int_min ν hint _).sub (int_min ν hint _)) (fun y => ?_)
  by_cases hy : y ∈ Set.Ioi (Q + h)
  · simp only [Set.indicator_of_mem hy]
    simp only [Set.mem_Ioi] at hy
    rw [min_eq_left hy.le, min_eq_left (by linarith)]; linarith
  · simp only [Set.indicator_of_notMem hy]
    have := min_le_min_right y (show Q ≤ Q + h by linarith)
    linarith

lemma sales_dec (hint : Integrable (fun x : ℝ => x) ν) (Q h : ℝ) (hh : 0 ≤ h) :
    CachonCoord.Newsvendor.expSales ν Q - CachonCoord.Newsvendor.expSales ν (Q - h) ≤
      h * ν.real (Set.Ioi (Q - h)) := by
  unfold CachonCoord.Newsvendor.expSales
  rw [← integral_sub (int_min ν hint _) (int_min ν hint _), mul_comm,
    ← smul_eq_mul, ← integral_indicator_const _ measurableSet_Ioi]
  refine integral_mono ((int_min ν hint _).sub (int_min ν hint _))
    ((integrable_const h).indicator measurableSet_Ioi) (fun y => ?_)
  by_cases hy : y ∈ Set.Ioi (Q - h)
  · simp only [Set.indicator_of_mem hy]
    have h1 : min Q y ≤ min (Q - h) y + h := by
      rcases le_total Q y with h2 | h2
      · rw [min_eq_left h2, min_eq_left (by linarith)]; linarith
      · rw [min_eq_right h2]; simp only [Set.mem_Ioi] at hy
        rw [min_eq_left hy.le]; linarith
    show min Q y - min (Q - h) y ≤ h
    linarith
  · simp only [Set.indicator_of_notMem hy]
    simp only [Set.mem_Ioi, not_lt] at hy
    show min Q y - min (Q - h) y ≤ 0
    rw [min_eq_right (by linarith), min_eq_right hy]; linarith

lemma reb_dec (hint : Integrable (fun x : ℝ => x) ν) (Q T h : ℝ) (hh : 0 ≤ h) :
    (∫ y, max (min Q y - T) 0 ∂ν) - (∫ y, max (min (Q - h) y - T) 0 ∂ν) ≤
      h * ν.real (Set.Ioi (Q - h)) := by
  rw [← integral_sub (int_reb ν hint _ _) (int_reb ν hint _ _), mul_comm,
    ← smul_eq_mul, ← integral_indicator_const _ measurableSet_Ioi]
  refine integral_mono ((int_reb ν hint _ _).sub (int_reb ν hint _ _))
    ((integrable_const h).indicator measurableSet_Ioi) (fun y => ?_)
  have hm : min (Q - h) y ≤ min Q y := min_le_min_right y (by linarith)
  have hmax : max (min Q y - T) 0 - max (min (Q - h) y - T) 0 ≤ min Q y - min (Q - h) y := by
    rcases le_total (min Q y - T) 0 with h1 | h1
    · rw [max_eq_right h1, max_eq_right (by linarith)]; linarith
    · rw [max_eq_left h1]; linarith [le_max_left (min (Q - h) y - T) 0]
  by_cases hy : y ∈ Set.Ioi (Q - h)
  · simp only [Set.indicator_of_mem hy]
    have h1 : min Q y ≤ min (Q - h) y + h := by
      rcases le_total Q y with h2 | h2
      · rw [min_eq_left h2, min_eq_left (by linarith)]; linarith
      · rw [min_eq_right h2]; simp only [Set.mem_Ioi] at hy
        rw [min_eq_left hy.le]; linarith
    show max (min Q y - T) 0 - max (min (Q - h) y - T) 0 ≤ h
    linarith
  · simp only [Set.indicator_of_notMem hy]
    simp only [Set.mem_Ioi, not_lt] at hy
    show max (min Q y - T) 0 - max (min (Q - h) y - T) 0 ≤ 0
    rw [min_eq_right (by linarith), min_eq_right hy]; linarith

lemma F_cont (hat : ∀ x, ν {x} = 0) (x : ℝ) :
    ContinuousAt (fun z => ν.real (Set.Ioi z)) x := by
  have hF : (fun z => ν.real (Set.Ioi z)) = fun z => 1 - cdf ν z := by
    ext z
    rw [cdf_eq_real, ← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
  rw [hF]
  apply ContinuousAt.sub continuousAt_const
  have hm := monotone_cdf ν
  rw [hm.continuousAt_iff_leftLim_eq_rightLim, StieltjesFunction.rightLim_eq]
  have h1 := (cdf ν).measure_singleton x
  rw [measure_cdf, hat x] at h1
  have h2 : cdf ν x - Function.leftLim (cdf ν) x ≤ 0 := ENNReal.ofReal_eq_zero.1 h1.symm
  have h3 := hm.leftLim_le (le_refl x)
  linarith


open Filter Topology in
lemma qinc (hint : Integrable (fun x : ℝ => x) ν) (hat : ∀ x, ν {x} = 0) (α β Qb : ℝ)
    (hQb : 0 ≤ Qb) (hβ : 0 ≤ β)
    (hopt : ∀ Q, 0 ≤ Q → -α * Q + β * CachonCoord.Newsvendor.expSales ν Q ≤
      -α * Qb + β * CachonCoord.Newsvendor.expSales ν Qb) :
    β * ν.real (Set.Ioi Qb) ≤ α := by
  have key : ∀ h, 0 < h → β * ν.real (Set.Ioi (Qb + h)) ≤ α := by
    intro h hh
    have h1 := hopt (Qb + h) (by linarith)
    have h2 := mul_le_mul_of_nonneg_left (sales_inc ν hint Qb h hh.le) hβ
    have h3 : h * (β * ν.real (Set.Ioi (Qb + h))) ≤ h * α := by nlinarith
    exact le_of_mul_le_mul_left h3 hh
  have ht : Tendsto (fun h => β * ν.real (Set.Ioi (Qb + h))) (𝓝[>] 0)
      (𝓝 (β * ν.real (Set.Ioi Qb))) := by
    apply Tendsto.const_mul
    have hc := (F_cont ν hat Qb).tendsto
    have hi : Tendsto (fun h : ℝ => Qb + h) (𝓝[>] 0) (𝓝 Qb) := by
      have h0 : Tendsto (fun h : ℝ => Qb + h) (𝓝 0) (𝓝 (Qb + 0)) :=
        tendsto_const_nhds.add tendsto_id
      rw [add_zero] at h0
      exact tendsto_nhdsWithin_of_tendsto_nhds h0
    exact hc.comp hi
  exact le_of_tendsto ht (eventually_nhdsWithin_of_forall (fun h hh => key h hh))

open Filter Topology in
lemma qdec (hint : Integrable (fun x : ℝ => x) ν) (hat : ∀ x, ν {x} = 0) (α β u T Qb : ℝ)
    (hQb : 0 < Qb) (hβ : 0 ≤ β) (hu : 0 ≤ u)
    (hopt : ∀ Q, 0 ≤ Q → -α * Q + β * CachonCoord.Newsvendor.expSales ν Q
        + u * (∫ y, max (min Q y - T) 0 ∂ν) ≤
      -α * Qb + β * CachonCoord.Newsvendor.expSales ν Qb + u * (∫ y, max (min Qb y - T) 0 ∂ν)) :
    α ≤ (β + u) * ν.real (Set.Ioi Qb) := by
  have key : ∀ h ∈ Set.Ioo 0 Qb, α ≤ (β + u) * ν.real (Set.Ioi (Qb - h)) := by
    intro h hh
    have h1 := hopt (Qb - h) (by linarith [hh.2])
    have h2 := mul_le_mul_of_nonneg_left (sales_dec ν hint Qb h hh.1.le) hβ
    have h3 := mul_le_mul_of_nonneg_left (reb_dec ν hint Qb T h hh.1.le) hu
    have h4 : h * α ≤ h * ((β + u) * ν.real (Set.Ioi (Qb - h))) := by nlinarith
    exact le_of_mul_le_mul_left h4 hh.1
  have ht : Tendsto (fun h => (β + u) * ν.real (Set.Ioi (Qb - h))) (𝓝[>] 0)
      (𝓝 ((β + u) * ν.real (Set.Ioi Qb))) := by
    apply Tendsto.const_mul
    have hc := (F_cont ν hat Qb).tendsto
    have hi : Tendsto (fun h : ℝ => Qb - h) (𝓝[>] 0) (𝓝 Qb) := by
      have h0 : Tendsto (fun h : ℝ => Qb - h) (𝓝 0) (𝓝 (Qb - 0)) :=
        tendsto_const_nhds.sub tendsto_id
      rw [sub_zero] at h0
      exact tendsto_nhdsWithin_of_tendsto_nhds h0
    exact hc.comp hi
  exact ge_of_tendsto ht (eventually_of_mem (Ioo_mem_nhdsGT hQb) key)

lemma ae_nonneg (hIio : ν (Set.Iio 0) = 0) : ∀ᵐ y ∂ν, 0 ≤ y := by
  rw [ae_iff]
  convert hIio using 2
  ext y; simp

lemma pos1 (hint : Integrable (fun x : ℝ => x) ν) (hIio : ν (Set.Iio 0) = 0)
    (hIoo : ∀ a b : ℝ, 0 ≤ a → a < b → 0 < ν (Set.Ioo a b)) (Qb : ℝ) (hQb : 0 < Qb) :
    0 < CachonCoord.Newsvendor.expSales ν Qb - Qb * ν.real (Set.Ioi Qb) := by
  unfold CachonCoord.Newsvendor.expSales
  rw [mul_comm, ← smul_eq_mul, ← integral_indicator_const _ measurableSet_Ioi,
    ← integral_sub (int_min ν hint _) ((integrable_const Qb).indicator measurableSet_Ioi)]
  have hint2 : Integrable (fun a => min Qb a - (Set.Ioi Qb).indicator (fun _ => Qb) a) ν :=
    (int_min ν hint Qb).sub ((integrable_const Qb).indicator measurableSet_Ioi)
  rw [integral_pos_iff_support_of_nonneg_ae _ hint2]
  · refine lt_of_lt_of_le (hIoo 0 Qb le_rfl hQb) (measure_mono (fun y hy => ?_))
    simp only [Set.mem_Ioo] at hy
    simp only [Function.mem_support, Pi.sub_apply, ne_eq]
    have hn : y ∉ Set.Ioi Qb := by simp only [Set.mem_Ioi, not_lt]; exact hy.2.le
    rw [Set.indicator_of_notMem hn, min_eq_right hy.2.le]
    linarith [hy.1]
  · filter_upwards [ae_nonneg ν hIio] with y hy
    simp only [Pi.zero_apply, Pi.sub_apply]
    by_cases h : y ∈ Set.Ioi Qb
    · rw [Set.indicator_of_mem h]; simp only [Set.mem_Ioi] at h
      rw [min_eq_left h.le]; simp
    · rw [Set.indicator_of_notMem h]; simp only [Set.mem_Ioi, not_lt] at h
      rw [min_eq_right h]; simpa using hy

lemma pos2 (hint : Integrable (fun x : ℝ => x) ν)
    (hIoo : ∀ a b : ℝ, 0 ≤ a → a < b → 0 < ν (Set.Ioo a b)) (T Qb : ℝ) (hT : 0 ≤ T)
    (hTQ : T < Qb) :
    0 < (∫ y, Set.indicator {y | T < min Qb y} (fun y => min Qb y) y ∂ν)
      - Qb * ν.real (Set.Ioi Qb) := by
  rw [mul_comm, ← smul_eq_mul, ← integral_indicator_const _ measurableSet_Ioi,
    ← integral_sub (int_ind ν hint _ _) ((integrable_const Qb).indicator measurableSet_Ioi)]
  have hint2 : Integrable (fun a => Set.indicator {y | T < min Qb y} (fun y => min Qb y) a
      - (Set.Ioi Qb).indicator (fun _ => Qb) a) ν :=
    (int_ind ν hint Qb T).sub ((integrable_const Qb).indicator measurableSet_Ioi)
  rw [integral_pos_iff_support_of_nonneg_ae _ hint2]
  · refine lt_of_lt_of_le (hIoo T Qb hT hTQ) (measure_mono (fun y hy => ?_))
    simp only [Set.mem_Ioo] at hy
    simp only [Function.mem_support, Pi.sub_apply, ne_eq]
    have hn : y ∉ Set.Ioi Qb := by simp only [Set.mem_Ioi, not_lt]; exact hy.2.le
    have hm : y ∈ {y | T < min Qb y} := by
      simp only [Set.mem_ofPred_eq]; rw [min_eq_right hy.2.le]; exact hy.1
    rw [Set.indicator_of_notMem hn, Set.indicator_of_mem hm, min_eq_right hy.2.le]
    linarith [hy.1]
  · refine ae_of_all _ (fun y => ?_)
    simp only [Pi.zero_apply, Pi.sub_apply]
    by_cases h : y ∈ Set.Ioi Qb
    · rw [Set.indicator_of_mem h]; simp only [Set.mem_Ioi] at h
      have hm : y ∈ {y | T < min Qb y} := by
        simp only [Set.mem_ofPred_eq]; rw [min_eq_left h.le]; exact hTQ
      rw [Set.indicator_of_mem hm, min_eq_left h.le]; simp
    · rw [Set.indicator_of_notMem h]
      by_cases h' : y ∈ {y | T < min Qb y}
      · rw [Set.indicator_of_mem h']; simp only [Set.mem_ofPred_eq] at h'
        simp only [sub_zero]; linarith [min_le_left Qb y]
      · rw [Set.indicator_of_notMem h']; simp

lemma M_zero (Qb T : ℝ) (h : Qb ≤ T) :
    (∫ y, Set.indicator {y | T < min Qb y} (fun y => min Qb y) y ∂ν) = 0 := by
  have : (Set.indicator {y | T < min Qb y} (fun y => min Qb y)) = fun _ => 0 := by
    ext y
    apply Set.indicator_of_notMem
    simp only [Set.mem_ofPred_eq, not_lt]
    linarith [min_le_left Qb y]
  rw [this, integral_zero]

end General

lemma ray (V : ℝ → ℝ) (d e K : ℝ) (hV : HasDerivAt V d e)
    (h : ∀ t : ℝ, 0 < t → t * K - V (t * e) ≤ K - V e) : K = e * d := by
  have hV' : HasDerivAt V d (1 * e) := by simpa using hV
  have h1 : HasDerivAt (fun t : ℝ => t * K - V (t * e)) (1 * K - d * (1 * e)) 1 :=
    ((hasDerivAt_id (1 : ℝ)).mul_const K).sub
      (HasDerivAt.comp (1 : ℝ) hV' ((hasDerivAt_id (1 : ℝ)).mul_const e))
  have hmax : IsLocalMax (fun t : ℝ => t * K - V (t * e)) 1 := by
    filter_upwards [Ioi_mem_nhds (one_pos : (0 : ℝ) < 1)] with t ht
    simpa using h t ht
  have := hmax.hasDerivAt_eq_zero h1
  linarith

section Scale

open ChannelRebate.NoCoord CachonCoord.Newsvendor

lemma sales_scale (D : Demand) (e t Q : ℝ) (ht : 0 < t) :
    expSales (D.effLaw (t * e)) (t * Q) = t * expSales (D.effLaw e) Q := by
  unfold expSales
  rw [effLaw_mul, integral_map (meas_mul t).aemeasurable (by fun_prop)]
  have : (fun y => min (t * Q) (t * y)) = fun y => t * min Q y := by
    ext y; rw [mul_min_of_nonneg _ _ ht.le]
  rw [this, integral_const_mul]

lemma left_scale (D : Demand) (e t Q : ℝ) (ht : 0 < t) :
    expLeftover (D.effLaw (t * e)) (t * Q) = t * expLeftover (D.effLaw e) Q := by
  unfold expLeftover
  rw [effLaw_mul, integral_map (meas_mul t).aemeasurable (by fun_prop)]
  have : (fun y => max (t * Q - t * y) 0) = fun y => t * max (Q - y) 0 := by
    ext y; rw [← mul_sub, mul_max_of_nonneg _ _ ht.le, mul_zero]
  rw [this, integral_const_mul]

lemma reb_scale (D : Demand) (e t T Q : ℝ) (ht : 0 < t) :
    expRebate D e T Q + (t - 1) *
      (∫ y, Set.indicator {y | T < min Q y} (fun y => min Q y) y ∂(D.effLaw e))
      ≤ expRebate D (t * e) T (t * Q) := by
  unfold expRebate
  rw [effLaw_mul, integral_map (meas_mul t).aemeasurable (by fun_prop),
    ← integral_const_mul, ← integral_add (int_reb _ (effLaw_integrable_id D e) _ _)
      ((int_ind _ (effLaw_integrable_id D e) _ _).const_mul _)]
  have hR : (fun y => max (min (t * Q) (t * y) - T) 0) =
      fun y => t * max (min Q y - T / t) 0 := by
    ext y
    rw [← mul_min_of_nonneg _ _ ht.le, mul_max_of_nonneg _ _ ht.le, mul_zero, mul_sub,
      mul_div_cancel₀ _ ht.ne']
  rw [hR]
  refine integral_mono (((int_reb _ (effLaw_integrable_id D e) _ _)).add
      ((int_ind _ (effLaw_integrable_id D e) _ _).const_mul _))
      ((int_reb _ (effLaw_integrable_id D e) Q (T / t)).const_mul t) (fun y => ?_)
  rw [mul_max_of_nonneg _ _ ht.le, mul_zero, mul_sub, mul_div_cancel₀ _ ht.ne']
  by_cases h : y ∈ {y | T < min Q y}
  · rw [Set.indicator_of_mem h]; simp only [Set.mem_ofPred_eq] at h
    rw [max_eq_left (by linarith)]
    have := le_max_left (t * min Q y - T) 0
    nlinarith
  · rw [Set.indicator_of_notMem h]; simp only [Set.mem_ofPred_eq, not_lt] at h
    rw [max_eq_right (by linarith)]; simp

end Scale

end RebP2

open ChannelRebate.NoCoord RebP2

theorem solution (p c s w : ℝ) (hc : 0 < c) (hcw : c < w) (hwp : w < p)
    (hsc : s < c) (D : Demand) (V : EffortCost)
    (Qbar ebar : ℝ) (hopt : ChannelRebate.Effort.IsOptimalPair (chainProfit p c s D V) Qbar ebar) (hebar : 0 < ebar) :
    (∀ b : ℝ, s ≤ b → b < w →
      ¬ ChannelRebate.Effort.IsOptimalPair (retailerProfit p w 0 b 0 D V) Qbar ebar) ∧
    (∀ u : ℝ, 0 < u →
      ¬ ChannelRebate.Effort.IsOptimalPair (retailerProfit p w u s 0 D V) Qbar ebar) ∧
    (∀ u T : ℝ, 0 < u → 0 ≤ T →
      ¬ ChannelRebate.Effort.IsOptimalPair (retailerProfit p w u s T D V) Qbar ebar) := by
  have hint := effLaw_integrable_id D ebar
  have hat := effLaw_singleton D hebar
  have hIio := effLaw_Iio D hebar
  have hIoo : ∀ a b : ℝ, 0 ≤ a → a < b → 0 < D.effLaw ebar (Set.Ioo a b) :=
    fun a b ha hab => effLaw_Ioo D hebar ha hab
  have hLe := leftover_eq (D.effLaw ebar) hint
  -- Q̄ > 0
  have hQpos : 0 < Qbar := by
    rcases hopt.1.lt_or_eq with h | h
    · exact h
    exfalso
    have h1 := hopt.2.2 0 le_rfl 0 le_rfl
    rw [← h] at h1
    unfold chainProfit at h1
    have hz1 : CachonCoord.Newsvendor.expSales (D.effLaw 0) 0 = 0 := by
      unfold CachonCoord.Newsvendor.expSales Demand.effLaw
      rw [integral_map (meas_mul 0).aemeasurable (by fun_prop)]; simp
    have hz2 : CachonCoord.Newsvendor.expLeftover (D.effLaw 0) 0 = 0 := by
      unfold CachonCoord.Newsvendor.expLeftover Demand.effLaw
      rw [integral_map (meas_mul 0).aemeasurable (by fun_prop)]; simp
    have hz3 : CachonCoord.Newsvendor.expSales (D.effLaw ebar) 0 = 0 := by
      unfold CachonCoord.Newsvendor.expSales
      apply integral_eq_zero_of_ae
      filter_upwards [ae_nonneg _ hIio] with y hy
      simp [min_eq_left hy]
    have hz4 : CachonCoord.Newsvendor.expLeftover (D.effLaw ebar) 0 = 0 := by
      unfold CachonCoord.Newsvendor.expLeftover
      apply integral_eq_zero_of_ae
      filter_upwards [ae_nonneg _ hIio] with y hy
      simp [hy]
    have hV : V.V 0 < V.V ebar :=
      V.strictMonoOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hebar.le) hebar
    rw [hz1, hz2, hz3, hz4, V.V_zero] at h1
    rw [V.V_zero] at hV
    linarith
  -- channel conditions
  have hchQ : ∀ Q, 0 ≤ Q → -(c - s) * Q + (p - s) * CachonCoord.Newsvendor.expSales (D.effLaw ebar) Q ≤
      -(c - s) * Qbar + (p - s) * CachonCoord.Newsvendor.expSales (D.effLaw ebar) Qbar := by
    intro Q hQ
    have := hopt.2.2 Q hQ ebar hopt.2.1
    unfold chainProfit at this
    rw [hLe, hLe] at this
    linarith
  have C1 := qinc _ hint hat (c - s) (p - s) Qbar hopt.1 (by linarith) hchQ
  set F := (D.effLaw ebar).real (Set.Ioi Qbar) with hF
  set Sb := CachonCoord.Newsvendor.expSales (D.effLaw ebar) Qbar with hSb
  have C2 : c - s ≤ (p - s + 0) * F := by
    refine qdec _ hint hat (c - s) (p - s) 0 0 Qbar hQpos (by linarith) le_rfl (fun Q hQ => ?_)
    have := hchQ Q hQ
    linarith
  have C3 : -c * Qbar + p * Sb + s * CachonCoord.Newsvendor.expLeftover (D.effLaw ebar) Qbar = ebar * V.dV ebar := by
    apply ray V.V (V.dV ebar) ebar _ (V.hasDerivAt ebar hebar)
    intro t ht
    have := hopt.2.2 (t * Qbar) (by positivity) (t * ebar) (by positivity)
    unfold chainProfit at this
    rw [sales_scale D ebar t Qbar ht, left_scale D ebar t Qbar ht] at this
    linarith
  rw [hLe] at C3
  have hA := pos1 _ hint hIio hIoo Qbar hQpos
  -- part 3 (target rebate alone)
  have part3 : ∀ u T : ℝ, 0 < u → 0 ≤ T →
      ¬ ChannelRebate.Effort.IsOptimalPair (retailerProfit p w u s T D V) Qbar ebar := by
    intro u T hu hT hR
    set M := ∫ y, Set.indicator {y | T < min Qbar y} (fun y => min Qbar y) y ∂(D.effLaw ebar)
      with hM
    have R3 : -w * Qbar + p * Sb + s * CachonCoord.Newsvendor.expLeftover (D.effLaw ebar) Qbar + u * M
        = ebar * V.dV ebar := by
      apply ray V.V (V.dV ebar) ebar _ (V.hasDerivAt ebar hebar)
      intro t ht
      have h1 := hR.2.2 (t * Qbar) (by positivity) (t * ebar) (by positivity)
      have h2 := mul_le_mul_of_nonneg_left (reb_scale D ebar t T Qbar ht) hu.le
      unfold retailerProfit at h1
      rw [sales_scale D ebar t Qbar ht, left_scale D ebar t Qbar ht] at h1
      rw [← hM] at h2
      nlinarith
    rw [hLe] at R3
    have huM : u * M = (w - c) * Qbar := by linarith
    rcases le_or_gt Qbar T with hQT | hQT
    · rw [hM, M_zero _ Qbar T hQT, mul_zero] at huM
      nlinarith
    · have R2 : w - s ≤ (p - s + u) * F := by
        refine qdec _ hint hat (w - s) (p - s) u T Qbar hQpos (by linarith) hu.le
          (fun Q hQ => ?_)
        have := hR.2.2 Q hQ ebar hopt.2.1
        unfold retailerProfit expRebate at this
        rw [hLe, hLe] at this
        linarith
      have hP := pos2 _ hint hIoo T Qbar hT hQT
      rw [← hM] at hP
      have h1 : 0 < u * (M - Qbar * F) := mul_pos hu hP
      have h2 : (w - c) * Qbar ≤ (u * F) * Qbar :=
        mul_le_mul_of_nonneg_right (by linarith) hQpos.le
      nlinarith
  refine ⟨?_, fun u hu => part3 u 0 hu le_rfl, part3⟩
  -- part 1 (returns alone)
  intro b hsb hbw hR
  have hRQ : ∀ Q, 0 ≤ Q → -(w - b) * Q + (p - b) * CachonCoord.Newsvendor.expSales (D.effLaw ebar) Q ≤
      -(w - b) * Qbar + (p - b) * CachonCoord.Newsvendor.expSales (D.effLaw ebar) Qbar := by
    intro Q hQ
    have := hR.2.2 Q hQ ebar hopt.2.1
    unfold retailerProfit at this
    rw [hLe, hLe] at this
    linarith
  have R1 := qinc _ hint hat (w - b) (p - b) Qbar hopt.1 (by linarith) hRQ
  have R2 : w - b ≤ (p - b + 0) * F := by
    refine qdec _ hint hat (w - b) (p - b) 0 0 Qbar hQpos (by linarith) le_rfl (fun Q hQ => ?_)
    have := hRQ Q hQ
    linarith
  have R3 : -w * Qbar + p * Sb + 0 * expRebate D ebar 0 Qbar
      + b * CachonCoord.Newsvendor.expLeftover (D.effLaw ebar) Qbar = ebar * V.dV ebar := by
    apply ray V.V (V.dV ebar) ebar _ (V.hasDerivAt ebar hebar)
    intro t ht
    have := hR.2.2 (t * Qbar) (by positivity) (t * ebar) (by positivity)
    unfold retailerProfit at this
    rw [sales_scale D ebar t Qbar ht, left_scale D ebar t Qbar ht] at this
    linarith
  rw [hLe, zero_mul, add_zero] at R3
  have E1 : (p - s) * F = c - s := by linarith
  have E2 : (p - b) * F = w - b := by linarith
  have hbs : (b - s) * (Sb - Qbar * F) = 0 := by
    nlinarith
  rcases mul_eq_zero.1 hbs with h | h
  · have : b = s := by linarith
    subst this
    linarith
  · linarith

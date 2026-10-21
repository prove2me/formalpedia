-- Prove2me | solution 1 for BoundedNV.Pooling.canon_profit_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:01:54.669978+00:00
-- url     : https://prove2.me/submissions/112f129c-2011-4fe6-bb59-f72ac0819596

import Mathlib
import Definitions.Def_BoundedNV_Pooling_Canonical
set_option autoImplicit false
open MeasureTheory ProbabilityTheory BoundedNV.Pooling

theorem BNP_demand_map (μ σ : ℝ) (hσ : 0 < σ) :
    InventoryControl.newsboyDemand μ σ = (gaussianReal 0 1).map (fun t => μ + σ * t) := by
  have h1 : (gaussianReal 0 1).map (fun t => μ + σ * t) =
      ((gaussianReal 0 1).map (σ * ·)).map (μ + ·) := by
    rw [Measure.map_map (measurable_const_add μ) (measurable_const_mul σ)]
    rfl
  rw [h1, gaussianReal_map_const_mul, gaussianReal_map_const_add]
  unfold InventoryControl.newsboyDemand
  congr 1
  · simp
  · apply NNReal.eq
    simp [Real.coe_toNNReal _ (sq_nonneg σ)]

theorem BNP_integrable_min (z : ℝ) : Integrable (fun t : ℝ => min t z) (gaussianReal 0 1) := by
  have hid : Integrable (fun t : ℝ => t) (gaussianReal 0 1) :=
    memLp_one_iff_integrable.1 (memLp_id_gaussianReal' 1 ENNReal.one_ne_top)
  exact hid.inf (integrable_const z)

theorem BNP_int_id : ∫ t : ℝ, t ∂(gaussianReal 0 1) = 0 := integral_id_gaussianReal

theorem BNP_m_le_zero (z : ℝ) : ∫ t : ℝ, min t z ∂(gaussianReal 0 1) ≤ 0 := by
  have hid : Integrable (fun t : ℝ => t) (gaussianReal 0 1) :=
    memLp_one_iff_integrable.1 (memLp_id_gaussianReal' 1 ENNReal.one_ne_top)
  calc ∫ t : ℝ, min t z ∂(gaussianReal 0 1) ≤ ∫ t : ℝ, t ∂(gaussianReal 0 1) :=
        integral_mono (BNP_integrable_min z) hid (fun t => min_le_left t z)
    _ = 0 := BNP_int_id

theorem BNP_m_le_z (z : ℝ) : ∫ t : ℝ, min t z ∂(gaussianReal 0 1) ≤ z := by
  calc ∫ t : ℝ, min t z ∂(gaussianReal 0 1) ≤ ∫ t : ℝ, z ∂(gaussianReal 0 1) :=
        integral_mono (BNP_integrable_min z) (integrable_const z) (fun t => min_le_right t z)
    _ = z := by simp

theorem BNP_m_ge (z : ℝ) :
    -(∫ t : ℝ, |t| ∂(gaussianReal 0 1) + |z|) ≤ ∫ t : ℝ, min t z ∂(gaussianReal 0 1) := by
  have hid : Integrable (fun t : ℝ => t) (gaussianReal 0 1) :=
    memLp_one_iff_integrable.1 (memLp_id_gaussianReal' 1 ENNReal.one_ne_top)
  have hn : Integrable (fun t : ℝ => -|t|) (gaussianReal 0 1) := hid.abs.neg
  have h1 : Integrable (fun t : ℝ => -|t| - |z|) (gaussianReal 0 1) :=
    hn.sub (integrable_const _)
  have := integral_mono h1 (BNP_integrable_min z) (fun t => by
    exact le_min (by linarith [neg_abs_le t, abs_nonneg z]) (by linarith [neg_abs_le z, abs_nonneg t]))
  have e : ∫ t : ℝ, (-|t| - |z|) ∂(gaussianReal 0 1) =
      -(∫ t : ℝ, |t| ∂(gaussianReal 0 1)) - |z| := by
    rw [integral_sub hn (integrable_const _), integral_neg]; simp
  rw [e] at this
  linarith

theorem BNP_m_mono : Monotone (fun z : ℝ => ∫ t : ℝ, min t z ∂(gaussianReal 0 1)) := by
  intro z z' h
  exact integral_mono (BNP_integrable_min z) (BNP_integrable_min z') (fun t => min_le_min_left t h)

theorem BNP_Pi_meas (p c : ℝ) : Measurable (canonProfit p c) := by
  unfold canonProfit
  exact (measurable_const.mul BNP_m_mono.measurable).sub (measurable_const.mul measurable_id)

theorem BNP_Pi_le (p c : ℝ) (hc : 0 < c) (hcp : c < p) (z : ℝ) :
    canonProfit p c z ≤ -(min c (p - c)) * |z| := by
  unfold canonProfit
  have hm0 := BNP_m_le_zero z
  have hmz := BNP_m_le_z z
  have h1 : min c (p - c) ≤ c := min_le_left _ _
  have h2 : min c (p - c) ≤ p - c := min_le_right _ _
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz]
    nlinarith [mul_nonneg (sub_nonneg.2 h1) hz]
  · rw [abs_of_nonpos hz]
    nlinarith [mul_nonneg (sub_nonneg.2 h2) (neg_nonneg.2 hz)]

theorem BNP_Pi_ge (p c : ℝ) (hc : 0 < c) (hcp : c < p) (z : ℝ) :
    -(canonProfit p c z) ≤ p * (∫ t : ℝ, |t| ∂(gaussianReal 0 1) + |z|) + c * |z| := by
  unfold canonProfit
  have := BNP_m_ge z
  nlinarith [neg_abs_le z, le_abs_self z]

theorem BNP_int_exp (k : ℝ) (hk : 0 < k) : Integrable (fun z : ℝ => Real.exp (-k * |z|)) := by
  have h1 : IntegrableOn (fun z : ℝ => Real.exp (-k * |z|)) (Set.Iic 0) := by
    refine (integrableOn_exp_mul_Iic hk 0).congr_fun (fun z hz => ?_) measurableSet_Iic
    simp only [Set.mem_Iic] at hz
    simp only [abs_of_nonpos hz]; ring_nf
  have h2 : IntegrableOn (fun z : ℝ => Real.exp (-k * |z|)) (Set.Ioi 0) := by
    refine (integrableOn_exp_mul_Ioi (by linarith : -k < 0) 0).congr_fun (fun z hz => ?_) measurableSet_Ioi
    simp only [Set.mem_Ioi] at hz
    simp only [abs_of_pos hz]
  have := h1.union h2
  rw [Set.Iic_union_Ioi] at this
  exact integrableOn_univ.1 this

theorem BNP_int_abs_exp (k : ℝ) (hk : 0 < k) : Integrable (fun z : ℝ => |z| * Real.exp (-k * |z|)) := by
  have hi := (BNP_int_exp (k / 2) (by linarith)).const_mul (2 / k)
  refine Integrable.mono' hi (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 : k * |z| / 2 ≤ Real.exp (k * |z| / 2) := by
    have := Real.add_one_le_exp (k * |z| / 2); linarith
  have h2 : Real.exp (-k * |z|) = Real.exp (k * |z| / 2) ^ (-1 : ℤ) * Real.exp (-(k/2) * |z|) := by
    rw [zpow_neg_one, ← Real.exp_neg, ← Real.exp_add]; congr 1; ring
  have h3 : |z| ≤ (2 / k) * Real.exp (k * |z| / 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hk]; nlinarith
  calc |z| * Real.exp (-k * |z|) ≤ (2 / k) * Real.exp (k * |z| / 2) * Real.exp (-k * |z|) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = (2 / k) * Real.exp (-(k / 2) * |z|) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem BNP_integ (p c β s : ℝ) (hc : 0 < c) (hcp : c < p) (hβ : 0 < β) (hs : 0 < s) :
    Integrable (fun z : ℝ => Real.exp (s * canonProfit p c z / β)) ∧
    Integrable (fun z : ℝ => canonProfit p c z * Real.exp (s * canonProfit p c z / β)) := by
  set κ := min c (p - c) with hκ
  have hκpos : 0 < κ := lt_min hc (by linarith)
  set k := s * κ / β with hk
  have hkpos : 0 < k := by positivity
  have hmeas : Measurable (fun z : ℝ => Real.exp (s * canonProfit p c z / β)) := by
    have := BNP_Pi_meas p c
    fun_prop
  have hbd : ∀ z : ℝ, Real.exp (s * canonProfit p c z / β) ≤ Real.exp (-k * |z|) := by
    intro z
    apply Real.exp_le_exp.2
    have := BNP_Pi_le p c hc hcp z
    rw [← hκ] at this
    have h3 : s * canonProfit p c z ≤ -(s * κ * |z|) := by
      nlinarith [mul_le_mul_of_nonneg_left this hs.le]
    calc s * canonProfit p c z / β ≤ -(s * κ * |z|) / β := div_le_div_of_nonneg_right h3 hβ.le
      _ = -k * |z| := by rw [hk]; field_simp
  have i1 : Integrable (fun z : ℝ => Real.exp (s * canonProfit p c z / β)) :=
    Integrable.mono' (BNP_int_exp k hkpos) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]; exact hbd z)
  refine ⟨i1, ?_⟩
  set C := ∫ t : ℝ, |t| ∂(gaussianReal 0 1) with hC
  have hC0 : 0 ≤ C := integral_nonneg (fun t => abs_nonneg t)
  have hdom : Integrable (fun z : ℝ => (p * C) * Real.exp (-k * |z|) + (p + c) * (|z| * Real.exp (-k * |z|))) :=
    ((BNP_int_exp k hkpos).const_mul _).add ((BNP_int_abs_exp k hkpos).const_mul _)
  refine Integrable.mono' hdom ((BNP_Pi_meas p c).mul hmeas).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  have hPneg : canonProfit p c z ≤ 0 := by
    have := BNP_Pi_le p c hc hcp z
    nlinarith [abs_nonneg z]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le, abs_of_nonpos hPneg]
  have := BNP_Pi_ge p c hc hcp z
  have he := hbd z
  have hep := Real.exp_pos (s * canonProfit p c z / β)
  calc -canonProfit p c z * Real.exp (s * canonProfit p c z / β)
      ≤ (p * (C + |z|) + c * |z|) * Real.exp (-k * |z|) :=
        mul_le_mul this he hep.le (by nlinarith [abs_nonneg z])
    _ = _ := by ring

theorem BNP_noatoms (z : ℝ) : gaussianReal 0 1 {z} = 0 :=
  gaussianReal_absolutelyContinuous 0 one_ne_zero (Real.volume_singleton)

theorem BNP_cdf_cont : Continuous (fun z : ℝ => cdf (gaussianReal 0 1) z) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  have e : ∀ z : ℝ, cdf (gaussianReal 0 1) z =
      ∫ t, (Set.Iic z).indicator (fun _ => (1:ℝ)) t ∂(gaussianReal 0 1) := by
    intro z
    rw [integral_indicator_const _ measurableSet_Iic, cdf_eq_real]
    simp
  simp only [e]
  refine continuousAt_of_dominated (bound := fun _ => (1:ℝ)) ?_ ?_ (integrable_const _) ?_
  · exact Filter.Eventually.of_forall fun z =>
      (measurable_const.indicator measurableSet_Iic).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => Filter.Eventually.of_forall fun t => ?_
    by_cases h : t ∈ Set.Iic z <;> simp [Set.indicator, h]
  · have hae : ∀ᵐ t ∂(gaussianReal 0 1), t ≠ z₀ := by
      rw [ae_iff]
      simpa using BNP_noatoms z₀
    filter_upwards [hae] with t ht
    rcases lt_or_gt_of_ne ht with h | h
    · refine (continuousAt_const (y := (1:ℝ))).congr ?_
      filter_upwards [eventually_gt_nhds h] with z hz
      simp [Set.indicator, hz.le]
    · refine (continuousAt_const (y := (0:ℝ))).congr ?_
      filter_upwards [eventually_lt_nhds h] with z hz
      have : ¬ t ≤ z := not_le.2 hz
      simp [Set.indicator, this]

theorem BNP_ioi_eq (z : ℝ) : (gaussianReal 0 1).real (Set.Ioi z) = 1 - cdf (gaussianReal 0 1) z := by
  rw [cdf_eq_real, ← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

theorem BNP_I1 (z z' : ℝ) (h : z < z') :
    (z' - z) * (1 - cdf (gaussianReal 0 1) z') ≤
        (∫ t : ℝ, min t z' ∂(gaussianReal 0 1)) - ∫ t : ℝ, min t z ∂(gaussianReal 0 1) ∧
    (∫ t : ℝ, min t z' ∂(gaussianReal 0 1)) - ∫ t : ℝ, min t z ∂(gaussianReal 0 1) ≤
        (z' - z) * (1 - cdf (gaussianReal 0 1) z) := by
  have hsub : (∫ t : ℝ, min t z' ∂(gaussianReal 0 1)) - ∫ t : ℝ, min t z ∂(gaussianReal 0 1) =
      ∫ t : ℝ, (min t z' - min t z) ∂(gaussianReal 0 1) :=
    (integral_sub (BNP_integrable_min z') (BNP_integrable_min z)).symm
  have hI1 : ∫ t : ℝ, (Set.Ioi z').indicator (fun _ => z' - z) t ∂(gaussianReal 0 1) =
      (z' - z) * (1 - cdf (gaussianReal 0 1) z') := by
    rw [integral_indicator_const _ measurableSet_Ioi, BNP_ioi_eq]; simp [mul_comm]
  have hI2 : ∫ t : ℝ, (Set.Ioi z).indicator (fun _ => z' - z) t ∂(gaussianReal 0 1) =
      (z' - z) * (1 - cdf (gaussianReal 0 1) z) := by
    rw [integral_indicator_const _ measurableSet_Ioi, BNP_ioi_eq]; simp [mul_comm]
  have hi1 : Integrable (fun t : ℝ => (Set.Ioi z').indicator (fun _ => z' - z) t) (gaussianReal 0 1) :=
    (integrable_const _).indicator measurableSet_Ioi
  have hi2 : Integrable (fun t : ℝ => (Set.Ioi z).indicator (fun _ => z' - z) t) (gaussianReal 0 1) :=
    (integrable_const _).indicator measurableSet_Ioi
  have hd : Integrable (fun t : ℝ => min t z' - min t z) (gaussianReal 0 1) :=
    (BNP_integrable_min z').sub (BNP_integrable_min z)
  rw [hsub]
  constructor
  · rw [← hI1]
    refine integral_mono hi1 hd (fun t => ?_)
    by_cases ht : z' < t
    · simp only [Set.indicator_of_mem (Set.mem_Ioi.2 ht)]
      rw [min_eq_right ht.le, min_eq_right (by linarith)]
    · simp only [Set.indicator_of_notMem (by simpa using ht : t ∉ Set.Ioi z')]
      rcases le_total t z with h1 | h1
      · rw [min_eq_left h1, min_eq_left (by linarith)]; simp
      · rw [min_eq_left (not_lt.1 ht), min_eq_right h1]; linarith
  · rw [← hI2]
    refine integral_mono hd hi2 (fun t => ?_)
    by_cases ht : z < t
    · simp only [Set.indicator_of_mem (Set.mem_Ioi.2 ht)]
      rcases le_total t z' with h1 | h1
      · rw [min_eq_left h1, min_eq_right ht.le]; linarith
      · rw [min_eq_right h1, min_eq_right ht.le]
    · simp only [Set.indicator_of_notMem (by simpa using ht : t ∉ Set.Ioi z)]
      rw [min_eq_left (not_lt.1 ht), min_eq_left (by linarith)]; simp

theorem BNP_max_cdf (p c : ℝ) (hc : 0 < c) (hcp : c < p) (z' : ℝ)
    (hmax : IsMaxOn (canonProfit p c) Set.univ z') :
    cdf (gaussianReal 0 1) z' = 1 - c / p := by
  have hp : 0 < p := by linarith
  have hmax' : ∀ w, canonProfit p c w ≤ canonProfit p c z' := fun w => hmax (Set.mem_univ w)
  have h1 : ∀ w, z' < w → 1 - c / p ≤ cdf (gaussianReal 0 1) w := by
    intro w hw
    obtain ⟨lo, _⟩ := BNP_I1 z' w hw
    have hm := hmax' w
    unfold canonProfit at hm
    have h3 : (w - z') * (p * (1 - cdf (gaussianReal 0 1) w) - c) ≤ 0 := by nlinarith
    have h4 : p * (1 - cdf (gaussianReal 0 1) w) - c ≤ 0 := by
      by_contra hneg
      push_neg at hneg
      nlinarith [mul_pos (sub_pos.2 hw) hneg]
    have : 1 - cdf (gaussianReal 0 1) w ≤ c / p := by rw [le_div_iff₀ hp]; linarith
    linarith
  have h2 : ∀ w, w < z' → cdf (gaussianReal 0 1) w ≤ 1 - c / p := by
    intro w hw
    obtain ⟨_, hi⟩ := BNP_I1 w z' hw
    have hm := hmax' w
    unfold canonProfit at hm
    have h3 : 0 ≤ (z' - w) * (p * (1 - cdf (gaussianReal 0 1) w) - c) := by nlinarith
    have h4 : 0 ≤ p * (1 - cdf (gaussianReal 0 1) w) - c := by
      by_contra hneg
      push_neg at hneg
      nlinarith [mul_pos (sub_pos.2 hw) (neg_pos.2 hneg)]
    have : c / p ≤ 1 - cdf (gaussianReal 0 1) w := by rw [div_le_iff₀ hp]; linarith
    linarith
  have hG := BNP_cdf_cont.continuousAt (x := z')
  have t1 : 1 - c / p ≤ cdf (gaussianReal 0 1) z' :=
    ge_of_tendsto (hG.tendsto.mono_left nhdsWithin_le_nhds : Filter.Tendsto _ (nhdsWithin z' (Set.Ioi z')) _)
      (eventually_nhdsWithin_of_forall fun w hw => h1 w hw)
  have t2 : cdf (gaussianReal 0 1) z' ≤ 1 - c / p :=
    le_of_tendsto (hG.tendsto.mono_left nhdsWithin_le_nhds : Filter.Tendsto _ (nhdsWithin z' (Set.Iio z')) _)
      (eventually_nhdsWithin_of_forall fun w hw => h2 w hw)
  exact le_antisymm t2 t1

theorem BNP_exists_max (p c : ℝ) (hc : 0 < c) (hcp : c < p) :
    ∃ z0 : ℝ, cdf (gaussianReal 0 1) z0 = 1 - c / p ∧ IsMaxOn (canonProfit p c) Set.univ z0 := by
  have hp : 0 < p := by linarith
  have hy0 : 0 < 1 - c / p := by
    have : c / p < 1 := by rw [div_lt_one hp]; exact hcp
    linarith
  have hy1 : 1 - c / p < 1 := by have : 0 < c / p := by positivity
                                 linarith
  have hrange : (1 - c / p) ∈ Set.range (fun z : ℝ => cdf (gaussianReal 0 1) z) := by
    refine mem_range_of_exists_le_of_exists_ge BNP_cdf_cont ?_ ?_
    · exact ((tendsto_cdf_atBot (μ := gaussianReal 0 1)).eventually (gt_mem_nhds hy0)).exists.imp fun a ha => ha.le
    · exact ((tendsto_cdf_atTop (μ := gaussianReal 0 1)).eventually (lt_mem_nhds hy1)).exists.imp fun a ha => ha.le
  obtain ⟨z0, hz0⟩ := hrange
  refine ⟨z0, hz0, ?_⟩
  intro w _
  simp only [Set.mem_setOf_eq]
  unfold canonProfit
  rcases lt_trichotomy w z0 with h | h | h
  · obtain ⟨lo, _⟩ := BNP_I1 w z0 h
    simp only at hz0
    rw [hz0, show (1:ℝ) - (1 - c / p) = c / p by ring] at lo
    have h5 : p * ((z0 - w) * (c / p)) = c * (z0 - w) := by field_simp
    nlinarith
  · rw [h]
  · obtain ⟨_, hi⟩ := BNP_I1 z0 w h
    simp only at hz0
    rw [hz0, show 1 - (1 - c / p) = c / p by ring] at hi
    have h5 : p * ((w - z0) * (c / p)) = c * (w - z0) := by field_simp
    nlinarith

theorem BNP_val (p c : ℝ) (hp : 0 < p) (z : ℝ) (hz : cdf (gaussianReal 0 1) z = 1 - c / p) :
    canonProfit p c z = p * ∫ v in Set.Iic z, v * gaussianPDFReal 0 1 v := by
  have hsplit : ∀ t : ℝ, min t z = (Set.Iic z).indicator (fun t => t) t + (Set.Ioi z).indicator (fun _ => z) t := by
    intro t
    by_cases h : t ≤ z
    · rw [min_eq_left h, Set.indicator_of_mem (Set.mem_Iic.2 h), Set.indicator_of_notMem (by simpa using h)]
      simp
    · push_neg at h
      rw [min_eq_right h.le, Set.indicator_of_notMem (by simpa using h), Set.indicator_of_mem (Set.mem_Ioi.2 h)]
      simp
  have hid : Integrable (fun t : ℝ => t) (gaussianReal 0 1) :=
    memLp_one_iff_integrable.1 (memLp_id_gaussianReal' 1 ENNReal.one_ne_top)
  have i1 : Integrable (fun t : ℝ => (Set.Iic z).indicator (fun t => t) t) (gaussianReal 0 1) :=
    hid.indicator measurableSet_Iic
  have i2 : Integrable (fun t : ℝ => (Set.Ioi z).indicator (fun _ => z) t) (gaussianReal 0 1) :=
    (integrable_const z).indicator measurableSet_Ioi
  have hm : ∫ t : ℝ, min t z ∂(gaussianReal 0 1) =
      (∫ t in Set.Iic z, t * gaussianPDFReal 0 1 t) + z * (c / p) := by
    simp only [hsplit]
    rw [integral_add i1 i2, integral_indicator_const _ measurableSet_Ioi, BNP_ioi_eq, hz]
    have : ∫ t : ℝ, (Set.Iic z).indicator (fun t => t) t ∂(gaussianReal 0 1) =
        ∫ t in Set.Iic z, t * gaussianPDFReal 0 1 t := by
      rw [integral_gaussianReal_eq_integral_smul one_ne_zero, ← integral_indicator measurableSet_Iic]
      congr 1; funext t
      by_cases h : t ∈ Set.Iic z
      · simp [Set.indicator_of_mem h, mul_comm]
      · simp [Set.indicator_of_notMem h]
    rw [this]; simp [mul_comm]
  unfold canonProfit
  rw [hm]
  field_simp
  ring

theorem solution (p c : ℝ) (hc : 0 < c) (hcp : c < p) :
    (∃ zstar : ℝ, IsMaxOn (canonProfit p c) Set.univ zstar) ∧
    (∀ zstar : ℝ, IsMaxOn (canonProfit p c) Set.univ zstar →
      cdf (gaussianReal 0 1) zstar = 1 - c / p ∧
        canonProfit p c zstar = p * ∫ v in Set.Iic zstar, v * gaussianPDFReal 0 1 v) ∧
    ∀ z : ℝ, canonProfit p c z ≤ 0 := by
  have hp : 0 < p := by linarith
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨z0, _, hz0⟩ := BNP_exists_max p c hc hcp
    exact ⟨z0, hz0⟩
  · intro z hz
    have h := BNP_max_cdf p c hc hcp z hz
    exact ⟨h, BNP_val p c hp z h⟩
  · intro z
    have := BNP_Pi_le p c hc hcp z
    have : 0 ≤ min c (p - c) * |z| := mul_nonneg (lt_min hc (by linarith)).le (abs_nonneg z)
    nlinarith


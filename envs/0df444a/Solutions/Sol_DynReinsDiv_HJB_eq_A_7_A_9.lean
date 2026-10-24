-- Prove2me | solution 1 for DynReinsDiv.HJB.eq_A_7_A_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T21:39:11.483988+00:00
-- url     : https://prove2.me/submissions/545e84fa-4481-4033-b626-13cb0788de7a

import Mathlib
import Definitions.Def_DynReinsDiv_HJB_Model

open MeasureTheory Set Filter Topology

namespace DynReinsDiv.HJB.Aux
open DynReinsDiv.HJB

variable (M : Model)

/-- survival function -/
noncomputable def h (t : ℝ) : ℝ := 1 - M.F t

lemma h_eq (t : ℝ) : h M t = M.μ.real (Ioi t) := by
  have := M.isProb
  unfold h Model.F claimCDF
  rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ]
  rfl

lemma h_nonneg (t : ℝ) : 0 ≤ h M t := by rw [h_eq]; exact measureReal_nonneg

lemma h_le_one (t : ℝ) : h M t ≤ 1 := by
  have := M.isProb
  rw [h_eq]; exact measureReal_le_one

lemma h_anti : Antitone (h M) := by
  intro a b hab
  have := M.isProb
  rw [h_eq, h_eq]
  exact measureReal_mono (Ioi_subset_Ioi hab)

lemma h_meas : Measurable (h M) := (h_anti M).measurable

lemma tail : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → h M t ≤ C / t ^ 3 := by
  obtain ⟨C, hC⟩ := M.tail_bound
  refine ⟨C, ?_, ?_⟩
  · have := hC 0 le_rfl; simpa using this
  · intro t ht
    have := hC t ht.le
    rw [le_div_iff₀ (by positivity)]
    have e : h M t = 1 - claimCDF M.μ t := rfl
    rw [e]; linarith [mul_comm (1 - claimCDF M.μ t) (t ^ 3)]

/-- a uniform constant -/
lemma bounds : ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 < t →
    h M t ≤ K / t ^ 2 ∧ t * h M t ≤ K / t ^ 2 ∧ t * h M t ≤ K / t ∧ t * (t * h M t) ≤ K ∧
      t * h M t ≤ K := by
  obtain ⟨C, hC0, hC⟩ := tail M
  refine ⟨1 + C, by linarith, fun t ht => ?_⟩
  have h0 := h_nonneg M t
  have h1 := h_le_one M t
  have h3 := hC t ht
  have h3' : t ^ 3 * h M t ≤ C := by
    rw [le_div_iff₀ (by positivity)] at h3; linarith
  rcases le_total t 1 with ht1 | ht1
  · have ht2 : t ^ 2 ≤ 1 := by nlinarith
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [le_div_iff₀ (by positivity)]; nlinarith
    · rw [le_div_iff₀ (by positivity)]; nlinarith
    · rw [le_div_iff₀ (by positivity)]; nlinarith
    · nlinarith
    · nlinarith
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [le_div_iff₀ (by positivity)]; nlinarith
    · rw [le_div_iff₀ (by positivity)]; nlinarith
    · rw [le_div_iff₀ (by positivity)]; nlinarith
    · nlinarith
    · have : t ≤ t ^ 3 := by nlinarith [mul_le_mul ht1 ht1 zero_le_one ht.le]
      nlinarith [mul_le_mul_of_nonneg_right this h0]

structure Good (k : ℝ → ℝ) (K : ℝ) : Prop where
  meas : Measurable k
  nonneg : ∀ t, 0 < t → 0 ≤ k t
  le_one : ∀ t, 0 < t → t ≤ 1 → k t ≤ 1
  sq : ∀ t, 0 < t → k t ≤ K / t ^ 2
  inv : ∀ t, 0 < t → k t ≤ K / t
  Kpos : 0 < K

namespace Good
variable {k : ℝ → ℝ} {K : ℝ} (hk : Good k K)
include hk

omit hk in
lemma rpow_eq {t : ℝ} (ht : 0 < t) : K / t ^ 2 = K * t ^ (-2 : ℝ) := by
  rw [Real.rpow_neg ht.le, div_eq_mul_inv]
  norm_cast

lemma intOn_Ioi {c : ℝ} (hc : 0 < c) : IntegrableOn k (Ioi c) := by
  have hi : IntegrableOn (fun t : ℝ => K * t ^ (-2 : ℝ)) (Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hc).const_mul K
  refine hi.mono' hk.meas.aestronglyMeasurable.restrict ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
  have ht' : 0 < t := hc.trans ht
  rw [Real.norm_eq_abs, abs_of_nonneg (hk.nonneg t ht'), ← rpow_eq ht']
  exact hk.sq t ht'

lemma intOn_Ioc01 : IntegrableOn k (Ioc 0 1) := by
  refine Measure.integrableOn_of_bounded (M := 1) (by simp) hk.meas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hk.nonneg t ht.1)]
  exact hk.le_one t ht.1 ht.2

lemma intOn_Ioi0 : IntegrableOn k (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
  exact hk.intOn_Ioc01.union (hk.intOn_Ioi one_pos)

lemma intOn_sub {s : Set ℝ} (hs : s ⊆ Ioi 0) : IntegrableOn k s := hk.intOn_Ioi0.mono_set hs

lemma setInt_nonneg {s : Set ℝ} (hs : MeasurableSet s) (hs0 : s ⊆ Ioi 0) :
    0 ≤ ∫ t in s, k t := by
  refine setIntegral_nonneg hs fun t ht => hk.nonneg t (hs0 ht)

lemma E_le {c : ℝ} (hc : 0 < c) : ∫ t in Ioi c, k t ≤ K / c := by
  have hi : IntegrableOn (fun t : ℝ => K * t ^ (-2 : ℝ)) (Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hc).const_mul K
  calc ∫ t in Ioi c, k t ≤ ∫ t in Ioi c, K * t ^ (-2 : ℝ) := by
        refine setIntegral_mono_on (hk.intOn_Ioi hc) hi measurableSet_Ioi fun t ht => ?_
        have ht' : 0 < t := hc.trans ht
        rw [← rpow_eq ht']; exact hk.sq t ht'
    _ = K / c := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hc]
        norm_num
        rw [Real.rpow_neg_one, div_eq_mul_inv]

lemma Ioc_le {c c' : ℝ} (hc : 0 < c) (hcc : c ≤ c') :
    ∫ t in Ioc c c', k t ≤ K / c - K / c' := by
  have hc' : 0 < c' := hc.trans_le hcc
  have hi : ∀ d, 0 < d → IntegrableOn (fun t : ℝ => K * t ^ (-2 : ℝ)) (Ioi d) := fun d hd =>
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hd).const_mul K
  have hval : ∀ d, 0 < d → ∫ t in Ioi d, K * t ^ (-2 : ℝ) = K / d := by
    intro d hd
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hd]
    norm_num
    rw [Real.rpow_neg_one, div_eq_mul_inv]
  have hsplit : ∫ t in Ioi c, K * t ^ (-2 : ℝ) =
      (∫ t in Ioc c c', K * t ^ (-2 : ℝ)) + ∫ t in Ioi c', K * t ^ (-2 : ℝ) := by
    rw [← Ioc_union_Ioi_eq_Ioi hcc, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      ((hi c hc).mono_set Ioc_subset_Ioi_self) (hi c' hc')]
  calc ∫ t in Ioc c c', k t ≤ ∫ t in Ioc c c', K * t ^ (-2 : ℝ) := by
        refine setIntegral_mono_on (hk.intOn_sub (fun t ht => hc.trans ht.1))
          ((hi c hc).mono_set Ioc_subset_Ioi_self) measurableSet_Ioc fun t ht => ?_
        have ht' : 0 < t := hc.trans ht.1
        rw [← rpow_eq ht']; exact hk.sq t ht'
    _ = K / c - K / c' := by rw [← hval c hc, ← hval c' hc', hsplit]; ring

lemma Ioc_le' {c c' : ℝ} (hc : 0 < c) (hcc : c ≤ c') :
    ∫ t in Ioc c c', k t ≤ (c' - c) * (K / c) := by
  calc ∫ t in Ioc c c', k t ≤ ∫ t in Ioc c c', K / c := by
        refine setIntegral_mono_on (hk.intOn_sub (fun t ht => hc.trans ht.1))
          (integrableOn_const (by simp)) measurableSet_Ioc fun t ht => ?_
        have ht' : 0 < t := hc.trans ht.1
        calc k t ≤ K / t := hk.inv t ht'
          _ ≤ K / c := div_le_div_of_nonneg_left hk.Kpos.le hc ht.1.le
    _ = (c' - c) * (K / c) := by
        rw [setIntegral_const, Real.volume_real_Ioc_of_le hcc, smul_eq_mul]

lemma split_Ioi {c c' : ℝ} (hc : 0 ≤ c) (hcc : c ≤ c') :
    ∫ t in Ioi c, k t = (∫ t in Ioc c c', k t) + ∫ t in Ioi c', k t := by
  rw [← Ioc_union_Ioi_eq_Ioi hcc, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hk.intOn_sub (fun t ht => lt_of_le_of_lt hc ht.1))
      (hk.intOn_sub (fun t ht => lt_of_le_of_lt (hc.trans hcc) ht))]

end Good


lemma ae_nonneg : ∀ᵐ z ∂M.μ, 0 ≤ z := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 ≤ a} = Iio 0 := by ext; simp
  rw [this]; exact M.claims_nonneg

lemma meas_lt_eq (t : ℝ) : M.μ {z : ℝ | t < z} = ENNReal.ofReal (h M t) := by
  have := M.isProb
  rw [h_eq, ofReal_measureReal (measure_ne_top _ _)]
  rfl

/-- layer cake, first moment form, as lintegral -/
lemma lc1 (f : ℝ → ℝ) (hf : Measurable f) (hnn : ∀ᵐ z ∂M.μ, 0 ≤ f z) :
    ∫⁻ z, ENNReal.ofReal (f z) ∂M.μ = ∫⁻ t in Ioi 0, M.μ {z | t < f z} :=
  lintegral_eq_lintegral_meas_lt M.μ hnn hf.aemeasurable

lemma lc2 (f : ℝ → ℝ) (hf : Measurable f) (hnn : ∀ᵐ z ∂M.μ, 0 ≤ f z) :
    ∫⁻ z, ENNReal.ofReal (f z ^ 2) ∂M.μ =
      ∫⁻ t in Ioi 0, M.μ {z | t < f z} * ENNReal.ofReal (2 * t) := by
  have := lintegral_comp_eq_lintegral_meas_lt_mul M.μ hnn hf.aemeasurable
    (g := fun t => 2 * t) (fun t _ => (continuous_const.mul continuous_id).intervalIntegrable _ _)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => by
      have : (0:ℝ) < t := ht
      linarith))
  rw [← this]
  congr 1; ext z
  congr 1
  rw [intervalIntegral.integral_const_mul, integral_id]
  ring


lemma int_eq1 (f : ℝ → ℝ) (hf : Measurable f) (hnn : ∀ᵐ z ∂M.μ, 0 ≤ f z) (φ : ℝ → ℝ)
    (hφ : ∀ t, 0 < t → M.μ {z | t < f z} = ENNReal.ofReal (φ t))
    (hφnn : ∀ t, 0 < t → 0 ≤ φ t) (hφi : IntegrableOn φ (Ioi 0)) :
    ∫ z, f z ∂M.μ = ∫ t in Ioi 0, φ t := by
  rw [integral_eq_lintegral_of_nonneg_ae hnn hf.aestronglyMeasurable, lc1 M f hf hnn,
    setLIntegral_congr_fun measurableSet_Ioi (fun t ht => hφ t ht),
    ← ofReal_integral_eq_lintegral_ofReal hφi
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => hφnn t ht)),
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioi fun t ht => hφnn t ht)]

lemma int_eq2 (f : ℝ → ℝ) (hf : Measurable f) (hnn : ∀ᵐ z ∂M.μ, 0 ≤ f z) (φ : ℝ → ℝ)
    (hφ : ∀ t, 0 < t → M.μ {z | t < f z} = ENNReal.ofReal (φ t))
    (hφnn : ∀ t, 0 < t → 0 ≤ φ t) (hφi : IntegrableOn (fun t => φ t * (2 * t)) (Ioi 0)) :
    ∫ z, f z ^ 2 ∂M.μ = ∫ t in Ioi 0, φ t * (2 * t) := by
  have hnn2 : 0 ≤ᵐ[M.μ] fun z => f z ^ 2 := Eventually.of_forall fun z => sq_nonneg _
  have hpos : ∀ t, 0 < t → 0 ≤ φ t * (2 * t) := fun t ht => by
    have := hφnn t ht; positivity
  rw [integral_eq_lintegral_of_nonneg_ae hnn2 (hf.pow_const 2).aestronglyMeasurable,
    lc2 M f hf hnn,
    setLIntegral_congr_fun measurableSet_Ioi (fun t ht => by
      rw [hφ t ht, ← ENNReal.ofReal_mul (hφnn t ht)]),
    ← ofReal_integral_eq_lintegral_ofReal hφi
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => hpos t ht)),
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioi fun t ht => hpos t ht)]

lemma goods : ∃ K : ℝ, Good (h M) K ∧ Good (fun t => t * h M t) K := by
  obtain ⟨K, hK, hb⟩ := bounds M
  refine ⟨K, ⟨h_meas M, fun t _ => h_nonneg M t, fun t _ _ => h_le_one M t,
    fun t ht => (hb t ht).1, fun t ht => ?_, hK⟩,
    ⟨measurable_id.mul (h_meas M), fun t ht => mul_nonneg ht.le (h_nonneg M t),
      fun t ht ht1 => ?_, fun t ht => (hb t ht).2.1, fun t ht => (hb t ht).2.2.1, hK⟩⟩
  · rw [le_div_iff₀ ht, mul_comm]; exact (hb t ht).2.2.2.2
  · have := h_le_one M t; have := h_nonneg M t; nlinarith

lemma mu1_eq : M.μ₁ = ∫ t in Ioi 0, h M t := by
  obtain ⟨K, gB, -⟩ := goods M
  exact int_eq1 M id measurable_id (ae_nonneg M) (h M) (fun t _ => meas_lt_eq M t)
    (fun t _ => h_nonneg M t) gB.intOn_Ioi0

lemma mu2_eq : M.μ₂ = 2 * ∫ t in Ioi 0, t * h M t := by
  obtain ⟨K, -, gA⟩ := goods M
  have := int_eq2 M id measurable_id (ae_nonneg M) (h M) (fun t _ => meas_lt_eq M t)
    (fun t _ => h_nonneg M t) (by
      have := gA.intOn_Ioi0.const_mul 2
      exact IntegrableOn.congr_fun this (fun t _ => by ring) measurableSet_Ioi)
  unfold Model.μ₂ claimSecondMoment
  simp only [id] at this
  rw [this, ← integral_const_mul]
  congr 1; ext t; ring

lemma meas_lt_min (a t : ℝ) : M.μ {z : ℝ | t < min z a} =
    ENNReal.ofReal ((Iio a).indicator (h M) t) := by
  by_cases hta : t < a
  · rw [indicator_of_mem (show t ∈ Iio a from hta), ← meas_lt_eq]
    congr 1; ext z; simp [hta]
  · have : {z : ℝ | t < min z a} = ∅ := by
      ext z; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, lt_min_iff, not_and]
      intro _; exact hta
    rw [this, measure_empty, indicator_of_notMem (show t ∉ Iio a from hta), ENNReal.ofReal_zero]

lemma ind_eq (a : ℝ) (ha : 0 < a) (g : ℝ → ℝ) :
    ∫ t in Ioi 0, (Iio a).indicator g t = ∫ t in Ioc 0 a, g t := by
  rw [setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio, integral_Ioc_eq_integral_Ioo]

lemma min1_eq (a : ℝ) (ha : 0 < a) : ∫ z, min z a ∂M.μ = ∫ t in Ioc 0 a, h M t := by
  obtain ⟨K, gB, -⟩ := goods M
  rw [← ind_eq a ha]
  refine int_eq1 M (fun z => min z a) (measurable_id.min measurable_const)
    ((ae_nonneg M).mono fun z hz => le_min hz ha.le) _ (fun t _ => meas_lt_min M a t)
    (fun t _ => indicator_nonneg (fun s _ => h_nonneg M s) t) ?_
  exact gB.intOn_Ioi0.indicator measurableSet_Iio

lemma min2_eq (a : ℝ) (ha : 0 < a) :
    ∫ z, (min z a) ^ 2 ∂M.μ = 2 * ∫ t in Ioc 0 a, t * h M t := by
  obtain ⟨K, -, gA⟩ := goods M
  have hfun : (fun t => (Iio a).indicator (h M) t * (2 * t)) =
      (Iio a).indicator (fun t => 2 * (t * h M t)) := by
    ext t; by_cases ht : t < a
    · simp [indicator_of_mem, ht]; ring
    · simp [indicator_of_notMem, ht]
  rw [int_eq2 M (fun z => min z a) (measurable_id.min measurable_const)
    ((ae_nonneg M).mono fun z hz => le_min hz ha.le) _ (fun t _ => meas_lt_min M a t)
    (fun t _ => indicator_nonneg (fun s _ => h_nonneg M s) t) ?_, hfun, ind_eq a ha,
    integral_const_mul]
  rw [hfun]
  exact (gA.intOn_Ioi0.const_mul 2).indicator measurableSet_Iio


noncomputable def Phi (k : ℝ → ℝ) (y : ℝ) : ℝ :=
  if 0 < y then (∫ t in Ioi 0, k t) - ∫ t in Ioi (1 / y), k t else ∫ t in Ioi 0, k t

namespace Good
variable {k : ℝ → ℝ} {K : ℝ} (hk : Good k K)
include hk

lemma E_nonneg {c : ℝ} (hc : 0 ≤ c) : 0 ≤ ∫ t in Ioi c, k t :=
  hk.setInt_nonneg measurableSet_Ioi (fun t ht => lt_of_le_of_lt hc ht)

lemma Phi_sub {y y' : ℝ} (hyy : y ≤ y') :
    0 ≤ Phi k y - Phi k y' ∧ Phi k y - Phi k y' ≤ K * (y' - y) := by
  unfold Phi
  by_cases hy' : 0 < y'
  · rw [if_pos hy']
    by_cases hy : 0 < y
    · rw [if_pos hy]
      have h1 : 1 / y' ≤ 1 / y := one_div_le_one_div_of_le hy hyy
      have hs := hk.split_Ioi (one_div_pos.2 hy').le h1
      have hb := hk.Ioc_le (one_div_pos.2 hy') h1
      have hn := hk.setInt_nonneg (s := Ioc (1 / y') (1 / y)) measurableSet_Ioc
        (fun t ht => lt_trans (one_div_pos.2 hy') ht.1)
      rw [div_div_eq_mul_div, div_div_eq_mul_div, div_one, div_one] at hb
      constructor <;> nlinarith
    · rw [if_neg hy]
      have hn := hk.E_nonneg (one_div_pos.2 hy').le
      have hb := hk.E_le (one_div_pos.2 hy')
      rw [div_div_eq_mul_div, div_one] at hb
      constructor <;> nlinarith [hk.Kpos]
  · have hy : ¬ 0 < y := fun h => hy' (lt_of_lt_of_le h hyy)
    rw [if_neg hy', if_neg hy]
    constructor <;> nlinarith [hk.Kpos]

lemma Phi_anti : Antitone (Phi k) := fun _ _ hyy => by
  have := (hk.Phi_sub hyy).1; linarith

lemma Phi_lip : LipschitzWith (Real.toNNReal K) (Phi k) := by
  refine LipschitzWith.of_dist_le_mul fun y y' => ?_
  rw [Real.coe_toNNReal _ hk.Kpos.le, Real.dist_eq, Real.dist_eq]
  rcases le_total y y' with hyy | hyy
  · have := hk.Phi_sub hyy
    rw [abs_of_nonneg this.1, abs_of_nonpos (by linarith)]; linarith
  · have := hk.Phi_sub hyy
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]; linarith

lemma Phi_pos {y : ℝ} (hy : 0 < y) : Phi k y = ∫ t in Ioc 0 (1 / y), k t := by
  unfold Phi; rw [if_pos hy, hk.split_Ioi le_rfl (one_div_pos.2 hy).le]; ring

end Good

noncomputable def cut (y z : ℝ) : ℝ := if 0 < y then min z (1 / y) else z

lemma A_cut (y : ℝ) : M.A y = 1 / 2 * ∫ z, (cut y z) ^ 2 ∂M.μ := by
  unfold Model.A cut
  by_cases hy : 0 < y
  · simp only [if_pos hy]
    rw [min2_eq M _ (one_div_pos.2 hy), intervalIntegral.integral_of_le (one_div_pos.2 hy).le,
      ← mul_assoc, one_div_mul_cancel two_ne_zero, one_mul]
    rfl
  · simp only [if_neg hy]
    unfold Model.μ₂ claimSecondMoment; ring

lemma B_cut (y : ℝ) : M.B y = ∫ z, cut y z ∂M.μ := by
  unfold Model.B cut
  by_cases hy : 0 < y
  · simp only [if_pos hy]
    rw [min1_eq M _ (one_div_pos.2 hy), intervalIntegral.integral_of_le (one_div_pos.2 hy).le]
    rfl
  · simp only [if_neg hy]
    rfl

lemma A_Phi (y : ℝ) : M.A y = Phi (fun t => t * h M t) y := by
  obtain ⟨K, -, gA⟩ := goods M
  by_cases hy : 0 < y
  · rw [gA.Phi_pos hy]
    unfold Model.A; rw [if_pos hy, intervalIntegral.integral_of_le (one_div_pos.2 hy).le]; rfl
  · unfold Phi Model.A; rw [if_neg hy, if_neg hy, mu2_eq]; ring

lemma B_Phi (y : ℝ) : M.B y = Phi (h M) y := by
  obtain ⟨K, gB, -⟩ := goods M
  by_cases hy : 0 < y
  · rw [gB.Phi_pos hy]
    unfold Model.B; rw [if_pos hy, intervalIntegral.integral_of_le (one_div_pos.2 hy).le]; rfl
  · unfold Phi Model.B; rw [if_neg hy, if_neg hy, mu1_eq]


lemma A_anti : Antitone M.A := by
  obtain ⟨K, -, gA⟩ := goods M
  intro a b hab; rw [A_Phi, A_Phi]; exact gA.Phi_anti hab

lemma B_anti : Antitone M.B := by
  obtain ⟨K, gB, -⟩ := goods M
  intro a b hab; rw [B_Phi, B_Phi]; exact gB.Phi_anti hab

lemma A_lip : ∃ K : NNReal, LipschitzWith K M.A := by
  obtain ⟨K, -, gA⟩ := goods M
  exact ⟨_, by have := gA.Phi_lip; rwa [show M.A = Phi _ from funext (A_Phi M)]⟩

lemma B_lip : ∃ K : NNReal, LipschitzWith K M.B := by
  obtain ⟨K, gB, -⟩ := goods M
  exact ⟨_, by have := gB.Phi_lip; rwa [show M.B = Phi _ from funext (B_Phi M)]⟩

lemma mu_Ioi_pos : 0 < M.μ (Ioi 0) := by
  have := M.isProb
  by_contra hcon
  have h0 : M.μ (Ioi 0) = 0 := le_antisymm (not_lt.1 hcon) (zero_le)
  have hae : ∀ᵐ z ∂M.μ, z = 0 := by
    have h1 : ∀ᵐ z ∂M.μ, z ∉ Ioi (0:ℝ) := measure_eq_zero_iff_ae_notMem.1 h0
    filter_upwards [h1, ae_nonneg M] with z hz hz'
    simp only [mem_Ioi, not_lt] at hz; linarith
  have : M.μ₁ = 0 := by
    unfold Model.μ₁ claimMean
    rw [integral_congr_ae hae]; simp
  have := M.γ_lt_mean; have := M.γ_pos
  unfold Model.μ₁ at *; linarith

lemma int_min (a : ℝ) (ha : 0 < a) (n : ℕ) : Integrable (fun z => (min z a) ^ n) M.μ := by
  have := M.isProb
  refine Integrable.of_bound ((measurable_id.min measurable_const).pow_const n).aestronglyMeasurable
    (a ^ n) ?_
  filter_upwards [ae_nonneg M] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_min hz ha.le) n)]
  exact pow_le_pow_left₀ (le_min hz ha.le) (min_le_right _ _) n

lemma int_min_pos (a : ℝ) (ha : 0 < a) (n : ℕ) : 0 < ∫ z, (min z a) ^ n ∂M.μ := by
  rw [integral_pos_iff_support_of_nonneg_ae _ (int_min M a ha n)]
  · refine lt_of_lt_of_le (mu_Ioi_pos M) (measure_mono fun z hz => ?_)
    have : 0 < min z a := lt_min hz ha
    exact (pow_pos this n).ne'
  · filter_upwards [ae_nonneg M] with z hz
    exact pow_nonneg (le_min hz ha.le) n

lemma int_min_le (a : ℝ) (ha : 0 < a) (n : ℕ) : ∫ z, (min z a) ^ n ∂M.μ ≤ a ^ n := by
  have := M.isProb
  have : ∫ z, (min z a) ^ n ∂M.μ ≤ ∫ _z, a ^ n ∂M.μ := by
    refine integral_mono_ae (int_min M a ha n) (integrable_const _) ?_
    filter_upwards [ae_nonneg M] with z hz
    exact pow_le_pow_left₀ (le_min hz ha.le) (min_le_right _ _) n
  simpa using this

lemma A_pos_bounds (y : ℝ) (hy : 0 < y) :
    0 < M.A y ∧ M.A y ≤ 1 / 2 * min (y ^ 2)⁻¹ M.μ₂ ∧ 0 < M.B y ∧ M.B y ≤ min y⁻¹ M.μ₁ := by
  have hA := A_cut M y
  have hB := B_cut M y
  unfold cut at hA hB
  simp only [if_pos hy] at hA hB
  have ha : 0 < 1 / y := one_div_pos.2 hy
  have h2 := int_min_pos M _ ha 2
  have h1 := int_min_pos M _ ha 1
  have l2 := int_min_le M _ ha 2
  have l1 := int_min_le M _ ha 1
  simp only [pow_one] at h1 l1
  have hA0 : M.A 0 = M.μ₂ / 2 := by unfold Model.A; simp
  have hB0 : M.B 0 = M.μ₁ := by unfold Model.B; simp
  have hAa := A_anti M hy.le
  have hBa := B_anti M hy.le
  refine ⟨by rw [hA]; positivity, ?_, by rw [hB]; exact h1, ?_⟩
  · rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2)]
    refine le_min ?_ (by linarith)
    rw [hA]; rw [div_pow, one_pow, one_div (y ^ 2)] at l2
    linarith
  · refine le_min ?_ (by linarith)
    rw [hB]; rwa [← one_div]

lemma A_deriv (y : ℝ) (hy : 0 < y) (hF : ContinuousAt M.F y⁻¹) :
    HasDerivAt M.A ((M.F y⁻¹ - 1) / y ^ 3) y ∧ HasDerivAt M.B ((M.F y⁻¹ - 1) / y ^ 2) y ∧
      M.F y⁻¹ - 1 ≤ 0 := by
  obtain ⟨K, gB, gA⟩ := goods M
  have hyi : 0 < y⁻¹ := inv_pos.2 hy
  have hev : ∀ᶠ y' in 𝓝 y, 0 < y' := lt_mem_nhds hy
  have hinv := hasDerivAt_inv hy.ne'
  refine ⟨?_, ?_, by have := h_nonneg M y⁻¹; unfold h at this; linarith⟩
  · have hII : IntervalIntegrable (fun t => t * (1 - M.F t)) volume 0 y⁻¹ := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hyi.le]
      exact gA.intOn_sub (fun t ht => ht.1)
    have hG := intervalIntegral.integral_hasDerivAt_right hII
      gA.meas.stronglyMeasurable.stronglyMeasurableAtFilter
      (continuousAt_id.mul (continuousAt_const.sub hF))
    have hc := hG.comp y hinv
    refine (hc.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [hev] with y' hy'
      unfold Model.A; rw [if_pos hy', one_div]; rfl
    · field_simp; ring
  · have hII : IntervalIntegrable (fun t => (1 - M.F t)) volume 0 y⁻¹ := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hyi.le]
      exact gB.intOn_sub (fun t ht => ht.1)
    have hG := intervalIntegral.integral_hasDerivAt_right hII
      gB.meas.stronglyMeasurable.stronglyMeasurableAtFilter
      (continuousAt_const.sub hF)
    have hc := hG.comp y hinv
    refine (hc.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [hev] with y' hy'
      unfold Model.B; rw [if_pos hy', one_div]; rfl
    · field_simp; ring

lemma AB_deriv_neg (y : ℝ) (hy : y < 0) : HasDerivAt M.A 0 y ∧ HasDerivAt M.B 0 y := by
  have hev : ∀ᶠ y' in 𝓝 y, y' < 0 := gt_mem_nhds hy
  constructor
  · refine (hasDerivAt_const y (M.μ₂ / 2)).congr_of_eventuallyEq ?_
    filter_upwards [hev] with y' hy'
    unfold Model.A; rw [if_neg (not_lt.2 hy'.le)]
  · refine (hasDerivAt_const y M.μ₁).congr_of_eventuallyEq ?_
    filter_upwards [hev] with y' hy'
    unfold Model.B; rw [if_neg (not_lt.2 hy'.le)]

end DynReinsDiv.HJB.Aux

open DynReinsDiv.HJB DynReinsDiv.HJB.Aux in
theorem solution (M : Model) :
    Antitone M.A ∧ Antitone M.B ∧
    (∃ K : NNReal, LipschitzWith K M.A) ∧ (∃ K : NNReal, LipschitzWith K M.B) ∧
    (∀ y : ℝ, 0 < y →
      0 < M.A y ∧ M.A y ≤ 1 / 2 * min (y ^ 2)⁻¹ M.μ₂ ∧
      0 < M.B y ∧ M.B y ≤ min y⁻¹ M.μ₁) ∧
    (∀ y : ℝ, 0 < y → ContinuousAt M.F y⁻¹ →
      HasDerivAt M.A ((M.F y⁻¹ - 1) / y ^ 3) y ∧
      HasDerivAt M.B ((M.F y⁻¹ - 1) / y ^ 2) y ∧
      M.F y⁻¹ - 1 ≤ 0) ∧
    (∀ y : ℝ, y < 0 → HasDerivAt M.A 0 y ∧ HasDerivAt M.B 0 y) :=
  ⟨A_anti M, B_anti M, A_lip M, B_lip M, A_pos_bounds M, A_deriv M, AB_deriv_neg M⟩

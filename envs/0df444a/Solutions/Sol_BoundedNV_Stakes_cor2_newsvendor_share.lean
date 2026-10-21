-- Prove2me | solution 1 for BoundedNV.Stakes.cor2_newsvendor_share
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:16:09.839575+00:00
-- url     : https://prove2.me/submissions/13447ae4-6516-4509-babe-9bec774bd3f3

import Mathlib
import Definitions.Def_BoundedNV_ExpFam_Logit
set_option autoImplicit false
open MeasureTheory BoundedNV.Uniform BoundedNV.ExpFam

theorem BNC_int (f : ℝ → ℝ) (hf : IsDemandDensity f) (x : ℝ) :
    Integrable (fun t => min t x * f t) := by
  refine Integrable.mono' (hf.integrable.const_mul |x|) ?_ (Filter.Eventually.of_forall fun t => ?_)
  · exact ((continuous_id.min continuous_const).aestronglyMeasurable).mul hf.integrable.1
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf.nonneg t)]
    by_cases ht : t < 0
    · simp [hf.zero_of_neg t ht]
    · push_neg at ht
      refine mul_le_mul_of_nonneg_right ?_ (hf.nonneg t)
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx]
        have : 0 ≤ min t x := le_min ht hx
        rw [abs_of_nonneg this]; exact min_le_right _ _
      · rw [min_eq_right (by linarith)]

theorem BNC_E_mono (f : ℝ → ℝ) (hf : IsDemandDensity f) : Monotone (expMin f) := by
  intro x y hxy
  exact integral_mono (BNC_int f hf x) (BNC_int f hf y)
    (fun t => mul_le_mul_of_nonneg_right (min_le_min_left t hxy) (hf.nonneg t))

theorem BNC_pi_meas (f : ℝ → ℝ) (hf : IsDemandDensity f) (p c : ℝ) : Measurable (nvProfit f p c) := by
  unfold nvProfit
  exact (measurable_const.mul (BNC_E_mono f hf).measurable).sub (measurable_const.mul measurable_id)

theorem BNC_E_nonneg (f : ℝ → ℝ) (hf : IsDemandDensity f) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ expMin f x ∧ expMin f x ≤ x := by
  constructor
  · refine integral_nonneg fun t => ?_
    by_cases ht : t < 0
    · simp [hf.zero_of_neg t ht]
    · exact mul_nonneg (le_min (not_lt.1 ht) hx) (hf.nonneg t)
  · calc expMin f x ≤ ∫ t, x * f t := integral_mono (BNC_int f hf x) (hf.integrable.const_mul x)
          (fun t => mul_le_mul_of_nonneg_right (min_le_right t x) (hf.nonneg t))
      _ = x := by rw [integral_const_mul, hf.integral_eq_one, mul_one]

theorem BNC_tail (f : ℝ → ℝ) (hf : IsDemandDensity f) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, 0 ≤ x → expMin f x ≤ M + x * ε := by
  have hlim : Filter.Tendsto (fun M : ℝ => ∫ t in Set.Iic M, f t) Filter.atTop (nhds (∫ t, f t)) := by
    have := tendsto_setIntegral_of_monotone (μ := volume) (f := f) (s := fun M : ℝ => Set.Iic M)
      (fun M => measurableSet_Iic) (fun a b h => Set.Iic_subset_Iic.2 h) hf.integrable.integrableOn
    have e : (⋃ n : ℝ, Set.Iic n) = Set.univ := by
      ext x; simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_univ, iff_true]; exact ⟨x, le_rfl⟩
    simpa [e] using this
  rw [hf.integral_eq_one] at hlim
  obtain ⟨M0, hM0⟩ := (Filter.eventually_atTop.1 (hlim.eventually (lt_mem_nhds (by linarith : 1 - ε < 1)))).imp
    fun a ha => ha
  set M := max M0 0 with hM
  have hMge : 1 - ε < ∫ t in Set.Iic M, f t := hM0 M (le_max_left _ _)
  have htail : ∫ t in Set.Ioi M, f t ≤ ε := by
    have := integral_add_compl (μ := volume) (measurableSet_Iic (a := M)) hf.integrable
    rw [hf.integral_eq_one, Set.compl_Iic] at this
    linarith
  refine ⟨M, le_max_right _ _, fun x hx => ?_⟩
  have hi1 : Integrable (fun t => M * f t) := hf.integrable.const_mul M
  have hi2 : Integrable (fun t => x * (Set.Ioi M).indicator f t) :=
    (hf.integrable.indicator measurableSet_Ioi).const_mul x
  calc expMin f x ≤ ∫ t, (M * f t + x * (Set.Ioi M).indicator f t) :=
        integral_mono (BNC_int f hf x) (hi1.add hi2) (fun t => by
          by_cases ht : t ≤ M
          · have : t ∉ Set.Ioi M := by simpa using ht
            rw [Set.indicator_of_notMem this]
            have h1 : min t x ≤ M := (min_le_left _ _).trans ht
            nlinarith [hf.nonneg t]
          · have : t ∈ Set.Ioi M := by simpa using ht
            rw [Set.indicator_of_mem this]
            have h1 : min t x ≤ x := min_le_right _ _
            have := hf.nonneg t
            have hM0' : 0 ≤ M := le_max_right _ _
            nlinarith)
    _ = M + x * ∫ t in Set.Ioi M, f t := by
        rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul, hf.integral_eq_one,
          integral_indicator measurableSet_Ioi]; ring
    _ ≤ M + x * ε := by nlinarith

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


theorem BNC_E_lip (f : ℝ → ℝ) (hf : IsDemandDensity f) (x y : ℝ) :
    |expMin f x - expMin f y| ≤ |x - y| := by
  have h1 : expMin f x - expMin f y = ∫ t, (min t x - min t y) * f t := by
    unfold expMin
    rw [← integral_sub (BNC_int f hf x) (BNC_int f hf y)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
  rw [h1]
  have := norm_integral_le_of_norm_le (hf.integrable.const_mul |x - y|) (f := fun t => (min t x - min t y) * f t)
    (Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf.nonneg t)]
      refine mul_le_mul_of_nonneg_right ?_ (hf.nonneg t)
      have := abs_min_sub_min_le_max t x t y
      simpa using this)
  rw [integral_const_mul, hf.integral_eq_one, mul_one, Real.norm_eq_abs] at this
  exact this

theorem BNC_pi_cont (f : ℝ → ℝ) (hf : IsDemandDensity f) (p c : ℝ) : Continuous (nvProfit f p c) := by
  have : Continuous (expMin f) := by
    have : LipschitzWith 1 (expMin f) := LipschitzWith.of_dist_le_mul fun x y => by
      simpa [Real.dist_eq] using BNC_E_lip f hf x y
    exact this.continuous
  unfold nvProfit
  fun_prop

theorem BNC_growth (f : ℝ → ℝ) (hf : IsDemandDensity f) (p c : ℝ) (hc : 0 < c) (hcp : c < p) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, 0 ≤ x →
      nvProfit f p c x ≤ p * M - c / 2 * x ∧ -(c * x) ≤ nvProfit f p c x := by
  have hp : 0 < p := by linarith
  obtain ⟨M, hM, hE⟩ := BNC_tail f hf (c / (2 * p)) (by positivity)
  refine ⟨M, hM, fun x hx => ⟨?_, ?_⟩⟩
  · have := hE x hx
    unfold nvProfit
    have h2 : p * (x * (c / (2 * p))) = c / 2 * x := by field_simp
    nlinarith
  · unfold nvProfit
    have := (BNC_E_nonneg f hf x hx).1
    nlinarith

theorem BNC_integ (f : ℝ → ℝ) (hf : IsDemandDensity f) (p c : ℝ) (hc : 0 < c) (hcp : c < p)
    (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun x => Real.exp (t * nvProfit f p c x)) (Set.Ici 0) ∧
    IntegrableOn (fun x => nvProfit f p c x * Real.exp (t * nvProfit f p c x)) (Set.Ici 0) := by
  obtain ⟨M, hM, hb⟩ := BNC_growth f hf p c hc hcp
  have hp : 0 < p := by linarith
  set k := t * c / 2 with hk
  have hkpos : 0 < k := by positivity
  have hmeas := BNC_pi_meas f hf p c
  have hbd : ∀ x : ℝ, 0 ≤ x → Real.exp (t * nvProfit f p c x) ≤ Real.exp (t * p * M) * Real.exp (-k * |x|) := by
    intro x hx
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    rw [abs_of_nonneg hx, hk]
    have := (hb x hx).1
    nlinarith
  have i1 : Integrable (fun x : ℝ => Real.exp (t * p * M) * Real.exp (-k * |x|)) :=
    (BNP_int_exp k hkpos).const_mul _
  have i2 : Integrable (fun x : ℝ => Real.exp (t * p * M) * (p * M * Real.exp (-k * |x|) + c * (|x| * Real.exp (-k * |x|)))) :=
    (((BNP_int_exp k hkpos).const_mul (p * M)).add ((BNP_int_abs_exp k hkpos).const_mul c)).const_mul _
  have hm1 : Measurable (fun x : ℝ => Real.exp (t * nvProfit f p c x)) := by fun_prop
  refine ⟨?_, ?_⟩
  · refine Integrable.mono' i1.integrableOn hm1.aestronglyMeasurable.restrict
      ((ae_restrict_iff' measurableSet_Ici).2 (Filter.Eventually.of_forall fun x hx => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact hbd x hx
  · refine Integrable.mono' i2.integrableOn ((hmeas.mul hm1).aestronglyMeasurable.restrict)
      ((ae_restrict_iff' measurableSet_Ici).2 (Filter.Eventually.of_forall fun x hx => ?_))
    have hx' : 0 ≤ x := hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    have h1 := hb x hx'
    have habs : |nvProfit f p c x| ≤ p * M + c * |x| := by
      rw [abs_of_nonneg hx']
      rw [abs_le]
      constructor
      · nlinarith [h1.2]
      · nlinarith [h1.1]
    have h2 := hbd x hx'
    calc |nvProfit f p c x| * Real.exp (t * nvProfit f p c x)
        ≤ (p * M + c * |x|) * (Real.exp (t * p * M) * Real.exp (-k * |x|)) :=
          mul_le_mul habs h2 (Real.exp_pos _).le (by positivity)
      _ = Real.exp (t * p * M) * (p * M * Real.exp (-k * |x|) + c * (|x| * Real.exp (-k * |x|))) := by ring

theorem BNC_I1 (f : ℝ → ℝ) (hf : IsDemandDensity f) (x y : ℝ) (h : x < y) :
    (y - x) * ∫ t in Set.Ioi y, f t ≤ expMin f y - expMin f x ∧
    expMin f y - expMin f x ≤ (y - x) * ∫ t in Set.Ioi x, f t := by
  have hsub : expMin f y - expMin f x = ∫ t, (min t y - min t x) * f t := by
    unfold expMin
    rw [← integral_sub (BNC_int f hf y) (BNC_int f hf x)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
  have hi : ∀ z : ℝ, Integrable (fun t => (y - x) * (Set.Ioi z).indicator f t) := fun z =>
    (hf.integrable.indicator measurableSet_Ioi).const_mul _
  have hd : Integrable (fun t => (min t y - min t x) * f t) :=
    ((BNC_int f hf y).sub (BNC_int f hf x)).congr (Filter.Eventually.of_forall fun t => by simp only [Pi.sub_apply]; ring)
  have e1 : ∫ t, (y - x) * (Set.Ioi y).indicator f t = (y - x) * ∫ t in Set.Ioi y, f t := by
    rw [integral_const_mul, integral_indicator measurableSet_Ioi]
  have e2 : ∫ t, (y - x) * (Set.Ioi x).indicator f t = (y - x) * ∫ t in Set.Ioi x, f t := by
    rw [integral_const_mul, integral_indicator measurableSet_Ioi]
  rw [hsub]
  constructor
  · rw [← e1]
    refine integral_mono (hi y) hd (fun t => ?_)
    have hft := hf.nonneg t
    by_cases ht : y < t
    · rw [Set.indicator_of_mem (Set.mem_Ioi.2 ht), min_eq_right ht.le, min_eq_right (by linarith)]
    · rw [Set.indicator_of_notMem (by simpa using ht)]
      rcases le_total t x with h1 | h1
      · rw [min_eq_left h1, min_eq_left (by linarith)]; simp
      · rw [min_eq_left (not_lt.1 ht), min_eq_right h1]; nlinarith
  · rw [← e2]
    refine integral_mono hd (hi x) (fun t => ?_)
    have hft := hf.nonneg t
    by_cases ht : x < t
    · rw [Set.indicator_of_mem (Set.mem_Ioi.2 ht)]
      rcases le_total t y with h1 | h1
      · rw [min_eq_left h1, min_eq_right ht.le]; nlinarith
      · rw [min_eq_right h1, min_eq_right ht.le]
    · rw [Set.indicator_of_notMem (by simpa using ht), min_eq_left (not_lt.1 ht), min_eq_left (by linarith)]
      simp

theorem BNC_nonconst (f : ℝ → ℝ) (hf : IsDemandDensity f) (p c : ℝ) (hc : 0 < c) (hcp : c < p) :
    ¬ ∃ k : ℝ, ∀ᵐ x ∂(volume.restrict (decisionDomain f)), nvProfit f p c x = k := by
  classical
  have hp : 0 < p := by linarith
  set S := decisionDomain f with hS
  have hconv : Convex ℝ S := convex_convexHull ℝ _
  have hsupp_pos : 0 < volume (Function.support f) := by
    rw [pos_iff_ne_zero]
    intro h0
    have hae : ∀ᵐ x ∂(volume : Measure ℝ), f x = 0 := by
      have := measure_eq_zero_iff_ae_notMem.1 h0
      filter_upwards [this] with x hx
      simpa using hx
    have : ∫ x, f x = 0 := integral_eq_zero_of_ae hae
    have h1 := hf.integral_eq_one
    linarith
  have hsub : Function.support f ⊆ S := subset_convexHull ℝ _
  rintro ⟨k, hk⟩
  set U := interior S with hU
  have hfront : volume (frontier S) = 0 := Convex.addHaar_frontier volume hconv
  have hSU : volume (S \ U) = 0 := by
    refine measure_mono_null ?_ hfront
    intro x hx
    exact ⟨subset_closure hx.1, hx.2⟩
  have hk' : ∀ᵐ x ∂(volume.restrict U), nvProfit f p c x = k :=
    ae_restrict_of_ae_restrict_of_subset interior_subset hk
  have hconst : ∀ x ∈ U, nvProfit f p c x = k :=
    Measure.eqOn_open_of_ae_eq (f := nvProfit f p c) (g := fun _ => k) hk' isOpen_interior
      (BNC_pi_cont f hf p c).continuousOn continuousOn_const
  -- tail function values
  have hT : ∀ y ∈ U, ∫ t in Set.Ioi y, f t = c / p := by
    intro y hy
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior y hy
    have hx : y - r / 2 ∈ U := hball (by simp [Real.dist_eq, abs_of_pos hr]; linarith)
    have hz : y + r / 2 ∈ U := hball (by simp [Real.dist_eq, abs_of_pos hr]; linarith)
    set x := y - r / 2
    set z := y + r / 2
    have hxy : x < y := by simp [x]; linarith
    have hyz : y < z := by simp [z]; linarith
    obtain ⟨a1, a2⟩ := BNC_I1 f hf x y hxy
    obtain ⟨b1, b2⟩ := BNC_I1 f hf y z hyz
    have ex := hconst x hx
    have ey := hconst y hy
    have ez := hconst z hz
    unfold nvProfit at ex ey ez
    have h1 : p * (expMin f y - expMin f x) = c * (y - x) := by linarith
    have h2 : p * (expMin f z - expMin f y) = c * (z - y) := by linarith
    have hpos1 : 0 < y - x := by linarith
    have hpos2 : 0 < z - y := by linarith
    apply le_antisymm
    · -- T y ≤ c/p
      rw [le_div_iff₀ hp]
      have : (y - x) * ((∫ t in Set.Ioi y, f t) * p) ≤ (y - x) * c := by nlinarith
      exact le_of_mul_le_mul_left this hpos1
    · rw [div_le_iff₀ hp]
      have : (z - y) * c ≤ (z - y) * ((∫ t in Set.Ioi y, f t) * p) := by nlinarith
      exact le_of_mul_le_mul_left this hpos2
  have hnull : ∀ x ∈ U, ∀ y ∈ U, x < y → ∫ t in Set.Ioc x y, f t = 0 := by
    intro x hx y hy hxy
    have hu : Set.Ioi x = Set.Ioc x y ∪ Set.Ioi y := by
      ext t; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro h; by_cases h2 : t ≤ y
        · exact Or.inl ⟨h, h2⟩
        · exact Or.inr (not_le.1 h2)
      · rintro (h | h); exact h.1; exact lt_trans hxy h
    have hdisj : Disjoint (Set.Ioc x y) (Set.Ioi y) := by
      rw [Set.disjoint_left]; intro t ht ht2; exact absurd ht.2 (not_le.2 ht2)
    have := setIntegral_union hdisj measurableSet_Ioi hf.integrable.integrableOn hf.integrable.integrableOn
    rw [← hu, hT x hx, hT y hy] at this
    linarith
  have hf0 : ∀ x ∈ U, ∀ y ∈ U, x < y → volume ({t | f t ≠ 0} ∩ Set.Ioc x y) = 0 := by
    intro x hx y hy hxy
    have h1 := (setIntegral_eq_zero_iff_of_nonneg_ae (μ := volume) (s := Set.Ioc x y) (f := f)
      (Filter.Eventually.of_forall fun t => hf.nonneg t) hf.integrable.integrableOn).1 (hnull x hx y hy hxy)
    have h2 := (ae_restrict_iff' measurableSet_Ioc).1 h1
    rw [ae_iff] at h2
    have : {a | ¬(a ∈ Set.Ioc x y → f a = (0 : ℝ → ℝ) a)} = {t | f t ≠ 0} ∩ Set.Ioc x y := by
      ext t; simp; tauto
    rw [this] at h2
    exact h2
  have hcover : volume ({t | f t ≠ 0} ∩ U) = 0 := by
    have hsubset : {t | f t ≠ 0} ∩ U ⊆ ⋃ q : ℚ, ⋃ r : ℚ,
        ({t | f t ≠ 0} ∩ (if (q : ℝ) ∈ U ∧ (r : ℝ) ∈ U ∧ (q : ℝ) < r then Set.Ioc (q : ℝ) r else ∅)) := by
      rintro t ⟨ht, htU⟩
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior t htU
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t - ε < t by linarith)
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show t < t + ε by linarith)
      have hqU : (q : ℝ) ∈ U := hball (by simp [Real.dist_eq, abs_lt]; constructor <;> linarith)
      have hrU : (r : ℝ) ∈ U := hball (by simp [Real.dist_eq, abs_lt]; constructor <;> linarith)
      simp only [Set.mem_iUnion]
      refine ⟨q, r, ht, ?_⟩
      have hqr : (q : ℝ) < r := by linarith
      rw [if_pos ⟨hqU, hrU, hqr⟩]
      exact ⟨hq2, hr1.le⟩
    refine measure_mono_null hsubset ?_
    refine measure_iUnion_null fun q => measure_iUnion_null fun r => ?_
    by_cases hc' : (q : ℝ) ∈ U ∧ (r : ℝ) ∈ U ∧ (q : ℝ) < r
    · rw [if_pos hc']
      exact hf0 _ hc'.1 _ hc'.2.1 hc'.2.2
    · rw [if_neg hc']
      simp
  have : volume (Function.support f) = 0 := by
    have hsp : Function.support f ⊆ ({t | f t ≠ 0} ∩ U) ∪ (S \ U) := by
      intro t ht
      by_cases htU : t ∈ U
      · exact Or.inl ⟨ht, htU⟩
      · exact Or.inr ⟨hsub ht, htU⟩
    refine measure_mono_null hsp ?_
    exact measure_union_null hcover hSU
  exact absurd this hsupp_pos.ne'

open MeasureTheory

/-- weighted Chebyshev-type core: integral over the product of the symmetrized integrand. -/
theorem BNS_cheb_core (μ : Measure ℝ) [SFinite μ] (g w1 w2 : ℝ → ℝ)
    (hw1 : Integrable w1 μ) (hw2 : Integrable w2 μ)
    (hg1 : Integrable (fun x => g x * w1 x) μ) (hg2 : Integrable (fun x => g x * w2 x) μ) :
    ∫ z : ℝ × ℝ, (g z.1 - g z.2) * (w1 z.1 * w2 z.2 - w1 z.2 * w2 z.1) ∂(μ.prod μ) =
      2 * ((∫ x, g x * w1 x ∂μ) * (∫ x, w2 x ∂μ) - (∫ x, g x * w2 x ∂μ) * (∫ x, w1 x ∂μ)) ∧
    Integrable (fun z : ℝ × ℝ => (g z.1 - g z.2) * (w1 z.1 * w2 z.2 - w1 z.2 * w2 z.1)) (μ.prod μ) := by
  have e : (fun z : ℝ × ℝ => (g z.1 - g z.2) * (w1 z.1 * w2 z.2 - w1 z.2 * w2 z.1)) =
      fun z => ((g z.1 * w1 z.1) * w2 z.2 - (g z.1 * w2 z.1) * w1 z.2) +
        (-(w1 z.1 * (g z.2 * w2 z.2)) + w2 z.1 * (g z.2 * w1 z.2)) := by
    funext z; ring
  have i1 : Integrable (fun z : ℝ × ℝ => (g z.1 * w1 z.1) * w2 z.2) (μ.prod μ) := hg1.mul_prod hw2
  have i2 : Integrable (fun z : ℝ × ℝ => (g z.1 * w2 z.1) * w1 z.2) (μ.prod μ) := hg2.mul_prod hw1
  have i3 : Integrable (fun z : ℝ × ℝ => w1 z.1 * (g z.2 * w2 z.2)) (μ.prod μ) := hw1.mul_prod hg2
  have i4 : Integrable (fun z : ℝ × ℝ => w2 z.1 * (g z.2 * w1 z.2)) (μ.prod μ) := hw2.mul_prod hg1
  have i12 : Integrable (fun z : ℝ × ℝ => (g z.1 * w1 z.1) * w2 z.2 - (g z.1 * w2 z.1) * w1 z.2)
      (μ.prod μ) := i1.sub i2
  have i34 : Integrable (fun z : ℝ × ℝ => -(w1 z.1 * (g z.2 * w2 z.2)) + w2 z.1 * (g z.2 * w1 z.2))
      (μ.prod μ) := i3.neg.add i4
  have i3n : Integrable (fun z : ℝ × ℝ => -(w1 z.1 * (g z.2 * w2 z.2))) (μ.prod μ) := i3.neg
  rw [e]
  refine ⟨?_, i12.add i34⟩
  have p1 : ∫ z : ℝ × ℝ, (g z.1 * w1 z.1) * w2 z.2 ∂(μ.prod μ) =
      (∫ x, g x * w1 x ∂μ) * ∫ x, w2 x ∂μ := integral_prod_mul (fun x => g x * w1 x) w2
  have p2 : ∫ z : ℝ × ℝ, (g z.1 * w2 z.1) * w1 z.2 ∂(μ.prod μ) =
      (∫ x, g x * w2 x ∂μ) * ∫ x, w1 x ∂μ := integral_prod_mul (fun x => g x * w2 x) w1
  have p3 : ∫ z : ℝ × ℝ, w1 z.1 * (g z.2 * w2 z.2) ∂(μ.prod μ) =
      (∫ x, w1 x ∂μ) * ∫ x, g x * w2 x ∂μ := integral_prod_mul w1 (fun x => g x * w2 x)
  have p4 : ∫ z : ℝ × ℝ, w2 z.1 * (g z.2 * w1 z.2) ∂(μ.prod μ) =
      (∫ x, w2 x ∂μ) * ∫ x, g x * w1 x ∂μ := integral_prod_mul w2 (fun x => g x * w1 x)
  rw [integral_add i12 i34, integral_sub i1 i2, integral_add i3n i4,
    integral_neg, p1, p2, p3, p4]
  ring

theorem BNS_pt (π g : ℝ → ℝ) (t1 t2 : ℝ) (ht : t2 < t1)
    (hg : ∀ x y, π x ≤ π y → g x ≤ g y) (x y : ℝ) :
    0 ≤ (g x - g y) * (Real.exp (t1 * π x) * Real.exp (t2 * π y) -
      Real.exp (t1 * π y) * Real.exp (t2 * π x)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  rcases le_total (π x) (π y) with h | h
  · have h1 := hg x y h
    have h2 : Real.exp (t1 * π x + t2 * π y) ≤ Real.exp (t1 * π y + t2 * π x) :=
      Real.exp_le_exp.2 (by nlinarith)
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  · have h1 := hg y x h
    have h2 : Real.exp (t1 * π y + t2 * π x) ≤ Real.exp (t1 * π x + t2 * π y) :=
      Real.exp_le_exp.2 (by nlinarith)
    exact mul_nonneg (by linarith) (by linarith)

theorem BNS_pt_strict (π : ℝ → ℝ) (t1 t2 : ℝ) (ht : t2 < t1) (x y : ℝ) (hxy : π x ≠ π y) :
    0 < (π x - π y) * (Real.exp (t1 * π x) * Real.exp (t2 * π y) -
      Real.exp (t1 * π y) * Real.exp (t2 * π x)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  rcases lt_or_gt_of_ne hxy with h | h
  · have h2 : Real.exp (t1 * π x + t2 * π y) < Real.exp (t1 * π y + t2 * π x) :=
      Real.exp_lt_exp.2 (by nlinarith)
    exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  · have h2 : Real.exp (t1 * π y + t2 * π x) < Real.exp (t1 * π x + t2 * π y) :=
      Real.exp_lt_exp.2 (by nlinarith)
    exact mul_pos (by linarith) (by linarith)

theorem BNS_cheb (μ : Measure ℝ) [SFinite μ] (π g : ℝ → ℝ) (t1 t2 : ℝ) (ht : t2 < t1)
    (hπ : Measurable π) (hgm : Measurable g)
    (hg : ∀ x y, π x ≤ π y → g x ≤ g y)
    (hw1 : Integrable (fun x => Real.exp (t1 * π x)) μ) (hw2 : Integrable (fun x => Real.exp (t2 * π x)) μ)
    (hg1 : Integrable (fun x => g x * Real.exp (t1 * π x)) μ)
    (hg2 : Integrable (fun x => g x * Real.exp (t2 * π x)) μ) :
    (∫ x, g x * Real.exp (t2 * π x) ∂μ) * (∫ x, Real.exp (t1 * π x) ∂μ) ≤
      (∫ x, g x * Real.exp (t1 * π x) ∂μ) * (∫ x, Real.exp (t2 * π x) ∂μ) := by
  obtain ⟨h1, h2⟩ := BNS_cheb_core μ g _ _ hw1 hw2 hg1 hg2
  have hnn : 0 ≤ ∫ z : ℝ × ℝ, (g z.1 - g z.2) * (Real.exp (t1 * π z.1) * Real.exp (t2 * π z.2) -
      Real.exp (t1 * π z.2) * Real.exp (t2 * π z.1)) ∂(μ.prod μ) := by
    refine integral_nonneg fun z => ?_
    exact BNS_pt π g t1 t2 ht hg z.1 z.2
  linarith


theorem BNS_e1 (lam β : ℝ) (π : ℝ → ℝ) (x : ℝ) :
    Real.exp (lam * π x / β) = Real.exp ((lam / β) * π x) := by
  congr 1; ring

theorem BNS_strict (μ : Measure ℝ) [SFinite μ] (π : ℝ → ℝ) (t1 t2 : ℝ) (ht : t2 < t1)
    (hw1 : Integrable (fun x => Real.exp (t1 * π x)) μ)
    (hw2 : Integrable (fun x => Real.exp (t2 * π x)) μ)
    (hg1 : Integrable (fun x => π x * Real.exp (t1 * π x)) μ)
    (hg2 : Integrable (fun x => π x * Real.exp (t2 * π x)) μ)
    (hnc : ¬ ∃ k : ℝ, ∀ᵐ x ∂μ, π x = k) :
    (∫ x, π x * Real.exp (t2 * π x) ∂μ) * (∫ x, Real.exp (t1 * π x) ∂μ) <
      (∫ x, π x * Real.exp (t1 * π x) ∂μ) * (∫ x, Real.exp (t2 * π x) ∂μ) := by
  obtain ⟨h1, h2⟩ := BNS_cheb_core μ π _ _ hw1 hw2 hg1 hg2
  have hF : ∀ z : ℝ × ℝ, 0 ≤ (π z.1 - π z.2) * (Real.exp (t1 * π z.1) * Real.exp (t2 * π z.2) -
      Real.exp (t1 * π z.2) * Real.exp (t2 * π z.1)) := fun z =>
    BNS_pt π π t1 t2 ht (fun x y h => h) z.1 z.2
  have hnn : 0 ≤ ∫ z : ℝ × ℝ, (π z.1 - π z.2) * (Real.exp (t1 * π z.1) * Real.exp (t2 * π z.2) -
      Real.exp (t1 * π z.2) * Real.exp (t2 * π z.1)) ∂(μ.prod μ) := integral_nonneg hF
  by_contra hcon
  push_neg at hcon
  have hI : ∫ z : ℝ × ℝ, (π z.1 - π z.2) * (Real.exp (t1 * π z.1) * Real.exp (t2 * π z.2) -
      Real.exp (t1 * π z.2) * Real.exp (t2 * π z.1)) ∂(μ.prod μ) = 0 := by linarith
  have hae := (integral_eq_zero_iff_of_nonneg (μ := μ.prod μ) hF h2).1 hI
  have hae2 : ∀ᵐ z ∂(μ.prod μ), π z.1 = π z.2 := by
    filter_upwards [hae] with z hz
    by_contra hne
    have := BNS_pt_strict π t1 t2 ht z.1 z.2 hne
    simp only [Pi.zero_apply] at hz
    linarith
  have hae3 := Measure.ae_ae_of_ae_prod hae2
  have : μ ≠ 0 := by
    rintro rfl
    exact hnc ⟨0, by simp⟩
  haveI : NeZero μ := ⟨this⟩
  obtain ⟨x0, hx0⟩ := hae3.exists
  exact hnc ⟨π x0, by filter_upwards [hx0] with y hy using hy.symm⟩

theorem BNS_mean_eq (S : Set ℝ) (hS : MeasurableSet S) (π : ℝ → ℝ) (lam β : ℝ) :
    BoundedNV.Uniform.logitExp S (fun x => lam * π x) β π =
      (∫ v in S, π v * Real.exp ((lam / β) * π v)) / ∫ v in S, Real.exp ((lam / β) * π v) := by
  unfold BoundedNV.Uniform.logitExp BoundedNV.Uniform.logitDensity
  have e : ∀ y, π y * S.indicator (fun y => Real.exp ((fun x => lam * π x) y / β) /
      ∫ v in S, Real.exp ((fun x => lam * π x) v / β)) y =
      S.indicator (fun y => π y * Real.exp ((lam / β) * π y) /
        ∫ v in S, Real.exp ((lam / β) * π v)) y := by
    intro y
    by_cases hy : y ∈ S
    · simp only [Set.indicator_of_mem hy, BNS_e1]
      ring
    · simp [Set.indicator_of_notMem hy]
  simp_rw [e]
  rw [integral_indicator hS, integral_div]

theorem solution (f : ℝ → ℝ) (hf : BoundedNV.ExpFam.IsDemandDensity f)
    (p c β lam₁ lam₂ : ℝ) (hc : 0 < c) (hcp : c < p) (hβ : 0 < β)
    (hlam₂ : 0 < lam₂) (hlam : lam₂ < lam₁) :
    BoundedNV.Uniform.logitExp (BoundedNV.ExpFam.decisionDomain f) (fun x => lam₂ * BoundedNV.Uniform.nvProfit f p c x) β (BoundedNV.Uniform.nvProfit f p c) <
      BoundedNV.Uniform.logitExp (BoundedNV.ExpFam.decisionDomain f) (fun x => lam₁ * BoundedNV.Uniform.nvProfit f p c x) β (BoundedNV.Uniform.nvProfit f p c) := by
  set S := decisionDomain f with hSdef
  have hconv : Convex ℝ S := convex_convexHull ℝ _
  have hSmeas : MeasurableSet S := (convex_iff_ordConnected.1 hconv).measurableSet
  have hSsub : S ⊆ Set.Ici 0 := by
    refine convexHull_min ?_ (convex_Ici 0)
    intro x hx
    by_contra hneg
    have : x < 0 := not_le.1 hneg
    exact hx (hf.zero_of_neg x this)
  rw [BNS_mean_eq S hSmeas, BNS_mean_eq S hSmeas]
  have ht2 : 0 < lam₂ / β := div_pos hlam₂ hβ
  have ht : lam₂ / β < lam₁ / β := div_lt_div_of_pos_right hlam hβ
  have ht1 : 0 < lam₁ / β := ht2.trans ht
  obtain ⟨i1, m1⟩ := BNC_integ f hf p c hc hcp (lam₁ / β) ht1
  obtain ⟨i2, m2⟩ := BNC_integ f hf p c hc hcp (lam₂ / β) ht2
  have i1' := i1.mono_set hSsub
  have i2' := i2.mono_set hSsub
  have m1' := m1.mono_set hSsub
  have m2' := m2.mono_set hSsub
  have hnc := BNC_nonconst f hf p c hc hcp
  have hne : NeZero (volume.restrict S) := ⟨by
    intro h
    exact hnc ⟨0, by rw [h, ae_zero]; exact Filter.eventually_bot⟩⟩
  have hZ1 := integral_exp_pos i1'
  have hZ2 := integral_exp_pos i2'
  have key := BNS_strict (volume.restrict S) (nvProfit f p c) (lam₁ / β) (lam₂ / β) ht i1' i2' m1' m2' hnc
  rw [div_lt_div_iff₀ hZ2 hZ1]
  exact key


-- Prove2me | solution 1 for BoundedNV.ExpFam.prop2_moments_from_logPartition
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T10:02:35.257764+00:00
-- url     : https://prove2.me/submissions/35d4ba47-5492-44e9-8677-152a2cddbcca

import Mathlib
import Definitions.Def_BoundedNV_ExpFam_Logit
import Definitions.Def_BoundedNV_ExpFam_LogPartition

set_option autoImplicit false

open MeasureTheory Filter Topology

open BoundedNV.ExpFam BoundedNV.Uniform in
lemma bnv1c_S_nonneg (f : ℝ → ℝ) (hf : IsDemandDensity f) :
    decisionDomain f ⊆ Set.Ici 0 := by
  unfold decisionDomain
  refine convexHull_min ?_ (convex_Ici 0)
  intro x hx
  by_contra h
  exact hx (hf.zero_of_neg x (by simpa using h))

open BoundedNV.ExpFam BoundedNV.Uniform in
lemma bnv1c_S_meas (f : ℝ → ℝ) : MeasurableSet (decisionDomain f) :=
  ((convex_convexHull ℝ _).ordConnected).measurableSet

open BoundedNV.ExpFam BoundedNV.Uniform in
lemma bnv1c_minf_int (f : ℝ → ℝ) (hf : IsDemandDensity f) (v : ℝ) :
    Integrable (fun t => min t v * f t) := by
  refine Integrable.mono' (hf.integrable.norm.const_mul |v|) ?_ ?_
  · exact ((continuous_id.min continuous_const).aestronglyMeasurable).mul
      hf.integrable.aestronglyMeasurable
  · refine Eventually.of_forall (fun t => ?_)
    simp only [norm_mul, Real.norm_eq_abs]
    rcases lt_or_ge t 0 with ht | ht
    · rw [hf.zero_of_neg t ht]; simp
    · have habs : |min t v| ≤ |v| := by
        rw [abs_le]; constructor
        · rcases le_total t v with h | h
          · rw [min_eq_left h]; linarith [abs_nonneg v]
          · rw [min_eq_right h]; exact neg_abs_le v
        · exact (min_le_right t v).trans (le_abs_self v)
      exact mul_le_mul_of_nonneg_right habs (abs_nonneg _)

open BoundedNV.ExpFam BoundedNV.Uniform in
lemma bnv1c_m_nonneg (f : ℝ → ℝ) (hf : IsDemandDensity f) {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ expMin f v := by
  unfold expMin
  refine integral_nonneg (fun t => ?_)
  rcases lt_or_ge t 0 with ht | ht
  · simp [hf.zero_of_neg t ht]
  · exact mul_nonneg (le_min ht hv) (hf.nonneg t)

open BoundedNV.ExpFam BoundedNV.Uniform in
lemma bnv1c_m_le_self (f : ℝ → ℝ) (hf : IsDemandDensity f) {v : ℝ} :
    expMin f v ≤ v := by
  unfold expMin
  calc ∫ t, min t v * f t ≤ ∫ t, v * f t :=
        integral_mono (bnv1c_minf_int f hf v) (hf.integrable.const_mul v)
          (fun t => mul_le_mul_of_nonneg_right (min_le_right _ _) (hf.nonneg t))
    _ = v := by rw [integral_const_mul, hf.integral_eq_one, mul_one]

open BoundedNV.ExpFam BoundedNV.Uniform in
lemma bnv1c_m_mono (f : ℝ → ℝ) (hf : IsDemandDensity f) : Monotone (expMin f) := by
  intro v w hvw
  unfold expMin
  exact integral_mono (bnv1c_minf_int f hf v) (bnv1c_minf_int f hf w)
    (fun t => mul_le_mul_of_nonneg_right (min_le_min le_rfl hvw) (hf.nonneg t))

open BoundedNV.ExpFam BoundedNV.Uniform in
lemma bnv1c_tail (f : ℝ → ℝ) (hf : IsDemandDensity f) :
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

open BoundedNV.ExpFam BoundedNV.Uniform in
lemma bnv1c_m_le (f : ℝ → ℝ) (hf : IsDemandDensity f) {a v : ℝ} (ha : 0 ≤ a) (hv : 0 ≤ v) :
    expMin f v ≤ a + v * ∫ t, (Set.Ioi a).indicator f t := by
  have hI : Integrable (fun t => a * f t + v * (Set.Ioi a).indicator f t) :=
    (hf.integrable.const_mul a).add ((hf.integrable.indicator measurableSet_Ioi).const_mul v)
  calc expMin f v ≤ ∫ t, (a * f t + v * (Set.Ioi a).indicator f t) := by
        unfold expMin
        refine integral_mono (bnv1c_minf_int f hf v) hI (fun t => ?_)
        have hft := hf.nonneg t
        by_cases ht : t ∈ Set.Ioi a
        · rw [Set.indicator_of_mem ht]
          have h1 : min t v ≤ v := min_le_right t v
          nlinarith [mul_nonneg ha hft, mul_le_mul_of_nonneg_right h1 hft]
        · rw [Set.indicator_of_notMem ht]
          have ht' : t ≤ a := by simpa using ht
          have h1 : min t v ≤ a := (min_le_left t v).trans ht'
          nlinarith [mul_le_mul_of_nonneg_right h1 hft]
    _ = a + v * ∫ t, (Set.Ioi a).indicator f t := by
        rw [integral_add (hf.integrable.const_mul a)
          ((hf.integrable.indicator measurableSet_Ioi).const_mul v),
          integral_const_mul, integral_const_mul, hf.integral_eq_one, mul_one]

lemma bnv1c_expbd {e K κ v : ℝ} (hκ : 0 < κ) (hv : 0 ≤ v) (he : e ≤ K - κ * v) :
    Real.exp e ≤ Real.exp K * Real.exp (-(κ/2) * v) ∧
    v * Real.exp e ≤ (2/κ) * Real.exp K * Real.exp (-(κ/2) * v) := by
  have h1 : Real.exp e ≤ Real.exp K * Real.exp (-κ * v) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-κ * v) ≤ Real.exp (-(κ/2) * v) := Real.exp_le_exp.mpr (by nlinarith)
  have hv2 : v ≤ (2/κ) * Real.exp ((κ/2) * v) := by
    have h := Real.add_one_le_exp ((κ/2) * v)
    calc v = (2/κ) * ((κ/2) * v) := by field_simp
      _ ≤ (2/κ) * Real.exp ((κ/2) * v) := by gcongr; linarith
  have h3 : Real.exp ((κ/2) * v) * Real.exp (-κ * v) = Real.exp (-(κ/2) * v) := by
    rw [← Real.exp_add]; congr 1; ring
  constructor
  · calc Real.exp e ≤ Real.exp K * Real.exp (-κ * v) := h1
      _ ≤ _ := by gcongr
  · calc v * Real.exp e ≤ v * (Real.exp K * Real.exp (-κ * v)) := by gcongr
      _ = Real.exp K * (v * Real.exp (-κ * v)) := by ring
      _ ≤ Real.exp K * ((2/κ) * Real.exp ((κ/2) * v) * Real.exp (-κ * v)) := by gcongr
      _ = (2/κ) * Real.exp K * (Real.exp ((κ/2) * v) * Real.exp (-κ * v)) := by ring
      _ = _ := by rw [h3]

open BoundedNV.ExpFam BoundedNV.Uniform in
lemma bnv1c_core (f : ℝ → ℝ) (hf : IsDemandDensity f) (η₁ η₂ : ℝ) (h1 : 0 < η₁) (h2 : 0 < η₂) :
    Integrable (fun v => Real.exp (η₁ * expMin f v - η₂ * v) * expMin f v)
      (volume.restrict (decisionDomain f)) ∧
    Integrable (fun v => Real.exp (η₁ * expMin f v - η₂ * v) * (-v))
      (volume.restrict (decisionDomain f)) ∧
    HasDerivAt (fun t => ∫ v in decisionDomain f, Real.exp (t * expMin f v - η₂ * v))
      (∫ v in decisionDomain f, Real.exp (η₁ * expMin f v - η₂ * v) * expMin f v) η₁ ∧
    HasDerivAt (fun s => ∫ v in decisionDomain f, Real.exp (η₁ * expMin f v - s * v))
      (∫ v in decisionDomain f, Real.exp (η₁ * expMin f v - η₂ * v) * (-v)) η₂ ∧
    0 < ∫ v in decisionDomain f, Real.exp (η₁ * expMin f v - η₂ * v) := by
  have hS := bnv1c_S_meas f
  have hSsub := bnv1c_S_nonneg f hf
  have hm : Measurable (expMin f) := (bnv1c_m_mono f hf).measurable
  -- choose the tail cut
  have hq : 0 < η₂ / (4 * η₁) := by positivity
  obtain ⟨a, haT, ha0⟩ := (((bnv1c_tail f hf).eventually (gt_mem_nhds hq)).and
    (eventually_ge_atTop 0)).exists
  set T := ∫ t, (Set.Ioi a).indicator f t with hTdef
  have hT0 : 0 ≤ T := integral_nonneg (fun t => Set.indicator_nonneg (fun t _ => hf.nonneg t) t)
  have hT : 4 * η₁ * T ≤ η₂ := by
    have := (lt_div_iff₀ (by positivity : (0:ℝ) < 4 * η₁)).mp haT
    linarith
  set κ := η₂ / 2 with hκdef
  have hκ : 0 < κ := by positivity
  set K := 2 * η₁ * a with hKdef
  -- exponent bounds
  have E1 : ∀ v ∈ decisionDomain f, ∀ t ∈ Metric.ball η₁ η₁,
      t * expMin f v - η₂ * v ≤ K - κ * v := by
    intro v hv t ht
    have hv0 : 0 ≤ v := hSsub hv
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
    have hm0 := bnv1c_m_nonneg f hf hv0
    have hmle := bnv1c_m_le f hf ha0 hv0
    have i1 : t * expMin f v ≤ 2 * η₁ * expMin f v :=
      mul_le_mul_of_nonneg_right (by linarith) hm0
    have i2 : 2 * η₁ * expMin f v ≤ 2 * η₁ * (a + v * T) :=
      mul_le_mul_of_nonneg_left hmle (by linarith)
    have i3 : v * (4 * η₁ * T) ≤ v * η₂ := mul_le_mul_of_nonneg_left hT hv0
    rw [hKdef, hκdef]
    nlinarith
  have E2 : ∀ v ∈ decisionDomain f, ∀ s ∈ Metric.ball η₂ (η₂ / 4),
      η₁ * expMin f v - s * v ≤ K - κ * v := by
    intro v hv s hs
    have hv0 : 0 ≤ v := hSsub hv
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    have hmle := bnv1c_m_le f hf ha0 hv0
    have i2 : η₁ * expMin f v ≤ η₁ * (a + v * T) := mul_le_mul_of_nonneg_left hmle h1.le
    have i3 : v * (4 * η₁ * T) ≤ v * η₂ := mul_le_mul_of_nonneg_left hT hv0
    have i4 : (3 * η₂ / 4) * v ≤ s * v := mul_le_mul_of_nonneg_right (by linarith) hv0
    have i5 : 0 ≤ η₁ * a := mul_nonneg h1.le ha0
    rw [hKdef, hκdef]
    nlinarith
  -- integrable dominating functions
  have hexpI : Integrable (fun v : ℝ => Real.exp (-(κ/2) * v)) (volume.restrict (decisionDomain f)) :=
    ((exp_neg_integrableOn_Ioi (-1) (half_pos hκ)).mono_set
      (hSsub.trans (Set.Ici_subset_Ioi.mpr (by norm_num))))
  have hB0 : Integrable (fun v : ℝ => Real.exp K * Real.exp (-(κ/2) * v))
      (volume.restrict (decisionDomain f)) := hexpI.const_mul _
  have hB : Integrable (fun v : ℝ => (2/κ) * Real.exp K * Real.exp (-(κ/2) * v))
      (volume.restrict (decisionDomain f)) := hexpI.const_mul _
  have hmeasF : ∀ t s : ℝ, AEStronglyMeasurable (fun v => Real.exp (t * expMin f v - s * v))
      (volume.restrict (decisionDomain f)) := by
    intro t s
    exact (Real.measurable_exp.comp ((hm.const_mul t).sub (measurable_id.const_mul s))).aestronglyMeasurable
  have hF0 : Integrable (fun v => Real.exp (η₁ * expMin f v - η₂ * v))
      (volume.restrict (decisionDomain f)) := by
    refine Integrable.mono' hB0 (hmeasF η₁ η₂) (ae_restrict_of_forall_mem hS (fun v hv => ?_))
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (bnv1c_expbd hκ (hSsub hv) (E1 v hv η₁ (Metric.mem_ball_self h1))).1
  -- derivative in the first coordinate
  have D1 := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (decisionDomain f))
    (F := fun t v => Real.exp (t * expMin f v - η₂ * v))
    (F' := fun t v => Real.exp (t * expMin f v - η₂ * v) * expMin f v)
    (x₀ := η₁) (bound := fun v => (2/κ) * Real.exp K * Real.exp (-(κ/2) * v))
    (Metric.ball_mem_nhds η₁ h1)
    (Eventually.of_forall (fun t => hmeasF t η₂)) hF0
    ((hmeasF η₁ η₂).mul hm.aestronglyMeasurable)
    (ae_restrict_of_forall_mem hS (fun v hv t ht => by
      have hv0 : 0 ≤ v := hSsub hv
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        abs_of_nonneg (bnv1c_m_nonneg f hf hv0)]
      calc Real.exp (t * expMin f v - η₂ * v) * expMin f v
          ≤ v * Real.exp (t * expMin f v - η₂ * v) := by
            rw [mul_comm]; exact mul_le_mul_of_nonneg_right (bnv1c_m_le_self f hf)
              (Real.exp_pos _).le
        _ ≤ _ := (bnv1c_expbd hκ hv0 (E1 v hv t ht)).2))
    hB
    (ae_restrict_of_forall_mem hS (fun v _ t _ =>
      ((hasDerivAt_mul_const (expMin f v)).sub_const (η₂ * v)).exp))
  -- derivative in the second coordinate
  have D2 := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (decisionDomain f))
    (F := fun s v => Real.exp (η₁ * expMin f v - s * v))
    (F' := fun s v => Real.exp (η₁ * expMin f v - s * v) * (-v))
    (x₀ := η₂) (bound := fun v => (2/κ) * Real.exp K * Real.exp (-(κ/2) * v))
    (Metric.ball_mem_nhds η₂ (by positivity : (0:ℝ) < η₂ / 4))
    (Eventually.of_forall (fun s => hmeasF η₁ s)) hF0
    ((hmeasF η₁ η₂).mul measurable_id.neg.aestronglyMeasurable)
    (ae_restrict_of_forall_mem hS (fun v hv s hs => by
      have hv0 : 0 ≤ v := hSsub hv
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        abs_neg, abs_of_nonneg hv0, mul_comm]
      exact (bnv1c_expbd hκ hv0 (E2 v hv s hs)).2))
    hB
    (ae_restrict_of_forall_mem hS (fun v _ s _ =>
      ((hasDerivAt_mul_const v).const_sub (η₁ * expMin f v)).exp))
  -- positivity of the partition function
  have hSpos : volume (decisionDomain f) ≠ 0 := by
    intro h0
    have h1' : ∫ x in decisionDomain f, f x = ∫ x, f x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        by_contra hne
        exact hx (subset_convexHull ℝ (Function.support f) hne))
    rw [Measure.restrict_eq_zero.mpr h0, integral_zero_measure, hf.integral_eq_one] at h1'
    norm_num at h1'
  have : NeZero (volume.restrict (decisionDomain f)) :=
    ⟨by rw [Ne, Measure.restrict_eq_zero]; exact hSpos⟩
  exact ⟨D1.1, D2.1, D1.2, D2.2, integral_exp_pos (f := fun v => η₁ * expMin f v - η₂ * v) hF0⟩

open BoundedNV.Uniform in
lemma bnv1c_logitExp_eq (S : Set ℝ) (hS : MeasurableSet S) (u g : ℝ → ℝ) (β : ℝ) :
    logitExp S u β g =
      (∫ y in S, g y * Real.exp (u y / β)) / ∫ v in S, Real.exp (u v / β) := by
  unfold logitExp logitDensity
  have : (fun y => g y * S.indicator
      (fun y => Real.exp (u y / β) / ∫ v in S, Real.exp (u v / β)) y) =
      S.indicator (fun y => g y * Real.exp (u y / β) / ∫ v in S, Real.exp (u v / β)) := by
    funext y
    by_cases hy : y ∈ S <;> simp [hy, mul_div_assoc]
  rw [this, integral_indicator hS, integral_div]

open BoundedNV.ExpFam in
theorem solution (f : ℝ → ℝ) (hf : IsDemandDensity f)
    (p c β : ℝ) (hβ : 0 < β) (hc : 0 < c) (hcp : c < p) :
    ∃ d₁ d₂ : ℝ,
      HasDerivAt (fun t => logPartition f t (c / β)) d₁ (p / β) ∧
      HasDerivAt (fun t => logPartition f (p / β) t) d₂ (c / β) ∧
      BoundedNV.Uniform.logitExp (decisionDomain f) (BoundedNV.Uniform.nvProfit f p c) β id = -d₂ ∧
      BoundedNV.Uniform.logitExp (decisionDomain f) (BoundedNV.Uniform.nvProfit f p c) β (BoundedNV.Uniform.nvProfit f p c) = p * d₁ + c * d₂ := by
  obtain ⟨hI1, hI2, hD1, hD2, hZ⟩ :=
    bnv1c_core f hf (p / β) (c / β) (div_pos (hc.trans hcp) hβ) (div_pos hc hβ)
  have hπ : ∀ v, BoundedNV.Uniform.nvProfit f p c v / β =
      p / β * BoundedNV.Uniform.expMin f v - c / β * v := by
    intro v; unfold BoundedNV.Uniform.nvProfit; ring
  refine ⟨(∫ v in decisionDomain f, Real.exp (p / β * BoundedNV.Uniform.expMin f v - c / β * v)
      * BoundedNV.Uniform.expMin f v) /
      ∫ v in decisionDomain f, Real.exp (p / β * BoundedNV.Uniform.expMin f v - c / β * v),
    (∫ v in decisionDomain f, Real.exp (p / β * BoundedNV.Uniform.expMin f v - c / β * v) * (-v)) /
      ∫ v in decisionDomain f, Real.exp (p / β * BoundedNV.Uniform.expMin f v - c / β * v),
    hD1.log hZ.ne', hD2.log hZ.ne', ?_, ?_⟩
  · rw [bnv1c_logitExp_eq _ (bnv1c_S_meas f)]
    simp only [hπ]
    have h : ∫ v in decisionDomain f,
        Real.exp (p / β * BoundedNV.Uniform.expMin f v - c / β * v) * (-v) =
        -∫ v in decisionDomain f,
          id v * Real.exp (p / β * BoundedNV.Uniform.expMin f v - c / β * v) := by
      rw [← integral_neg]; congr 1; funext v; simp only [id]; ring
    rw [h, neg_div, neg_neg]
  · rw [bnv1c_logitExp_eq _ (bnv1c_S_meas f)]
    simp only [hπ]
    have h4 : ∫ y in decisionDomain f, BoundedNV.Uniform.nvProfit f p c y *
        Real.exp (p / β * BoundedNV.Uniform.expMin f y - c / β * y) =
        p * (∫ y in decisionDomain f,
          Real.exp (p / β * BoundedNV.Uniform.expMin f y - c / β * y) *
            BoundedNV.Uniform.expMin f y) +
        c * (∫ y in decisionDomain f,
          Real.exp (p / β * BoundedNV.Uniform.expMin f y - c / β * y) * (-y)) := by
      rw [← integral_const_mul, ← integral_const_mul,
        ← integral_add (hI1.const_mul p) (hI2.const_mul c)]
      congr 1; funext y; unfold BoundedNV.Uniform.nvProfit; ring
    rw [h4]; ring

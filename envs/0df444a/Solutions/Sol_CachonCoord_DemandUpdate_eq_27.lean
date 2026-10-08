-- Prove2me | solution 1 for CachonCoord.DemandUpdate.eq_27
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:22:23.509237+00:00
-- url     : https://prove2.me/submissions/f1170c44-4809-4ecd-8ec2-cc2a63ba590a

import Mathlib
import Definitions.Def_CachonCoord_DemandUpdate_Model

open MeasureTheory ProbabilityTheory


namespace CachonCoord.DemandUpdate

noncomputable def expSales (D : Measure ℝ) (q : ℝ) : ℝ := ∫ d, min q d ∂D
noncomputable def expLeftover (D : Measure ℝ) (q : ℝ) : ℝ := ∫ d, max (q - d) 0 ∂D
noncomputable def meanDemand (D : Measure ℝ) : ℝ := ∫ d, d ∂D

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

lemma du_nsc (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : Continuous (cdf μ)) :
    NullSingletonClass μ := by
  refine ⟨fun x => ?_⟩
  rw [← measure_cdf μ, StieltjesFunction.measure_singleton]
  have : Function.leftLim (cdf μ) x = cdf μ x :=
    leftLim_eq_of_tendsto ((h.tendsto x).mono_left nhdsWithin_le_nhds)
  rw [this]; simp

namespace Model
variable (M : Model)

lemma S_eq (ξ : ℝ) : M.S ξ = expSales (M.D ξ) := rfl

lemma S_deriv {ξ : ℝ} (hξ : 0 ≤ ξ) (q : ℝ) : HasDerivAt (M.S ξ) (1 - M.F ξ q) q := by
  haveI := M.isProb ξ hξ
  haveI := du_nsc (M.D ξ) (M.continuous_cdf ξ hξ)
  exact nv_S_deriv (M.D ξ) (M.integrable ξ hξ) (M.nonneg ξ hξ) q

lemma F_nonpos {ξ : ℝ} (hξ : 0 ≤ ξ) (x : ℝ) (hx : x ≤ 0) : M.F ξ x = 0 := by
  haveI := M.isProb ξ hξ
  haveI := du_nsc (M.D ξ) (M.continuous_cdf ξ hξ)
  exact nv_cdf_nonpos (M.D ξ) (M.nonneg ξ hξ) x hx

lemma ratio_pos : 0 < M.ratio := by
  unfold Model.ratio; have := M.c2_pos; have := M.c2_lt_p
  exact div_pos (by linarith) (by linarith)

lemma ratio_lt_one : M.ratio < 1 := by
  unfold Model.ratio; have := M.c2_pos; have := M.c2_lt_p
  rw [div_lt_one (by linarith)]; linarith

lemma F_mono {ξ : ℝ} : Monotone (M.F ξ) := fun a b h => (cdf (M.D ξ)).mono h

lemma F_cont {ξ : ℝ} (hξ : 0 ≤ ξ) : Continuous (M.F ξ) := M.continuous_cdf ξ hξ

lemma F_smono {ξ : ℝ} (hξ : 0 ≤ ξ) : StrictMonoOn (M.F ξ) (Set.Ici 0) := M.strictMono_cdf ξ hξ

lemma pos_of_F {ξ a : ℝ} (hξ : 0 ≤ ξ) (hFa : M.F ξ a = M.ratio) : 0 < a := by
  by_contra h; push_neg at h
  have := M.F_nonpos hξ a h; have := M.ratio_pos; linarith

lemma qstar_exists {ξ : ℝ} (hξ : 0 ≤ ξ) : ∃ qs, 0 < qs ∧ M.F ξ qs = M.ratio := by
  haveI := M.isProb ξ hξ
  have ht : Filter.Tendsto (M.F ξ) Filter.atTop (nhds 1) := tendsto_cdf_atTop (M.D ξ)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (ht.eventually (lt_mem_nhds M.ratio_lt_one))
  have hN' := hN (max N 0) (le_max_left _ _)
  obtain ⟨c, hc, hFc⟩ := intermediate_value_Icc (le_max_right N 0) (M.F_cont hξ).continuousOn
    (show M.ratio ∈ Set.Icc (M.F ξ 0) (M.F ξ (max N 0)) from
      ⟨by rw [M.F_nonpos hξ 0 le_rfl]; exact M.ratio_pos.le, hN'.le⟩)
  exact ⟨c, M.pos_of_F hξ hFc, hFc⟩

lemma F_uniq {ξ a b : ℝ} (hξ : 0 ≤ ξ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hFa : M.F ξ a = M.ratio)
    (hFb : M.F ξ b = M.ratio) : a = b :=
  (M.F_smono hξ).injOn ha hb (hFa.trans hFb.symm)

lemma O2_deriv {ξ : ℝ} (hξ : 0 ≤ ξ) (q1 q : ℝ) :
    HasDerivAt (M.Omega2 q1 ξ) (M.p * (1 - M.F ξ q) - M.c2) q := by
  have h := (((M.S_deriv hξ q).const_mul M.p).sub ((hasDerivAt_id q).const_mul M.c2)).add_const
    (M.c2 * q1)
  have he : M.Omega2 q1 ξ = fun q => M.p * M.S ξ q - M.c2 * id q + M.c2 * q1 := by
    funext q; rfl
  rw [he]; exact h.congr_deriv (by ring)

lemma deriv_pos_iff (x : ℝ) : 0 < M.p * (1 - x) - M.c2 ↔ x < M.ratio := by
  unfold Model.ratio; have := M.c2_pos; have := M.c2_lt_p
  rw [lt_div_iff₀ (by linarith)]; constructor <;> intro h <;> nlinarith

lemma deriv_neg_iff (x : ℝ) : M.p * (1 - x) - M.c2 < 0 ↔ M.ratio < x := by
  unfold Model.ratio; have := M.c2_pos; have := M.c2_lt_p
  rw [div_lt_iff₀ (by linarith)]; constructor <;> intro h <;> nlinarith

lemma O2_cont {ξ : ℝ} (hξ : 0 ≤ ξ) (q1 : ℝ) : Continuous (M.Omega2 q1 ξ) :=
  continuous_iff_continuousAt.2 fun q => (M.O2_deriv hξ q1 q).continuousAt

lemma O2_smono {ξ qs : ℝ} (hξ : 0 ≤ ξ) (hqs : 0 ≤ qs) (hF : M.F ξ qs = M.ratio) (q1 : ℝ) :
    StrictMonoOn (M.Omega2 q1 ξ) (Set.Iic qs) := by
  apply strictMonoOn_of_deriv_pos (convex_Iic qs) (M.O2_cont hξ q1).continuousOn
  intro x hx
  rw [interior_Iic] at hx
  rw [(M.O2_deriv hξ q1 x).deriv, M.deriv_pos_iff]
  rcases le_or_gt x 0 with h | h
  · rw [M.F_nonpos hξ x h]; exact M.ratio_pos
  · rw [← hF]; exact M.F_smono hξ (le_of_lt h) hqs hx

lemma O2_santi {ξ qs : ℝ} (hξ : 0 ≤ ξ) (hqs : 0 ≤ qs) (hF : M.F ξ qs = M.ratio) (q1 : ℝ) :
    StrictAntiOn (M.Omega2 q1 ξ) (Set.Ici qs) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici qs) (M.O2_cont hξ q1).continuousOn
  intro x hx
  rw [interior_Ici] at hx
  rw [(M.O2_deriv hξ q1 x).deriv, M.deriv_neg_iff, ← hF]
  exact M.F_smono hξ hqs (le_of_lt (lt_of_le_of_lt hqs hx)) hx

lemma O2_max_at {ξ qs : ℝ} (hξ : 0 ≤ ξ) (hqs : 0 ≤ qs) (hF : M.F ξ qs = M.ratio) (q1 : ℝ) :
    IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) (max q1 qs) := by
  intro y hy
  simp only [Set.mem_Ici] at hy
  show M.Omega2 q1 ξ y ≤ M.Omega2 q1 ξ (max q1 qs)
  rcases le_total q1 qs with h | h
  · rw [max_eq_right h]
    rcases le_total y qs with h' | h'
    · exact (M.O2_smono hξ hqs hF q1).monotoneOn (Set.mem_Iic.2 h') (Set.mem_Iic.2 le_rfl) h'
    · exact (M.O2_santi hξ hqs hF q1).antitoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h') h'
  · rw [max_eq_left h]
    exact (M.O2_santi hξ hqs hF q1).antitoneOn (Set.mem_Ici.2 h) (Set.mem_Ici.2 (h.trans hy)) hy

lemma O2_max_uniq {ξ qs : ℝ} (hξ : 0 ≤ ξ) (hqs : 0 ≤ qs) (hF : M.F ξ qs = M.ratio) (q1 q : ℝ)
    (hq : q1 ≤ q) (hmax : IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) q) : q = max q1 qs := by
  by_contra hne
  have hm := hmax (show max q1 qs ∈ Set.Ici q1 from Set.mem_Ici.2 (le_max_left _ _))
  simp only [Set.mem_setOf_eq] at hm
  rcases lt_or_gt_of_ne hne with h | h
  · -- q < max q1 qs, so q < qs
    have hqq : q < qs := by
      rcases le_total q1 qs with h' | h'
      · rwa [max_eq_right h'] at h
      · rw [max_eq_left h'] at h; linarith
    have := (M.O2_smono hξ hqs hF q1) (Set.mem_Iic.2 (le_of_lt hqq)) (Set.mem_Iic.2 (le_refl qs)) hqq
    have h2 : max q1 qs = qs := max_eq_right (by linarith)
    rw [h2] at hm; linarith
  · have := (M.O2_santi hξ hqs hF q1) (Set.mem_Ici.2 (le_max_right q1 qs))
      (Set.mem_Ici.2 (le_of_lt ((le_max_right q1 qs).trans_lt h))) h
    linarith

end Model

namespace Model
variable (M : Model)

noncomputable def Kf (ξ : ℝ) : Measure ℝ := if 0 ≤ ξ then M.D ξ else Measure.dirac 0

lemma Kf_meas : Measurable M.Kf := by
  unfold Model.Kf
  exact Measurable.piecewise measurableSet_Ici M.measurable_D measurable_const

noncomputable def K : Kernel ℝ ℝ := ⟨M.Kf, M.Kf_meas⟩

lemma K_eq {ξ : ℝ} (hξ : 0 ≤ ξ) : M.K ξ = M.D ξ := by
  show M.Kf ξ = M.D ξ
  unfold Model.Kf; simp [hξ]

instance K_markov : IsMarkovKernel M.K := by
  refine ⟨fun ξ => ?_⟩
  show IsProbabilityMeasure (M.Kf ξ)
  unfold Model.Kf
  by_cases h : 0 ≤ ξ
  · simp only [h, if_true]; exact M.isProb ξ h
  · simp only [h, if_false]; infer_instance

noncomputable def qsel (q2sel : ℝ → ℝ → ℝ) (q1 ξ : ℝ) : ℝ := if 0 ≤ ξ then q2sel q1 ξ else 0

lemma q2sel_eq {q2sel : ℝ → ℝ → ℝ} (hq2 : M.IsChainPeriod2Optimal q2sel) {q1 ξ : ℝ}
    (hq1 : 0 ≤ q1) (hξ : 0 ≤ ξ) :
    ∃ qs, 0 < qs ∧ M.F ξ qs = M.ratio ∧ q2sel q1 ξ = max q1 qs := by
  obtain ⟨qs, hqs, hF⟩ := M.qstar_exists hξ
  obtain ⟨h1, h2⟩ := hq2 q1 ξ hq1 hξ
  exact ⟨qs, hqs, hF, M.O2_max_uniq hξ hqs.le hF q1 _ h1 h2⟩

lemma q2sel_le_iff {q2sel : ℝ → ℝ → ℝ} (hq2 : M.IsChainPeriod2Optimal q2sel) {q1 ξ : ℝ}
    (hq1 : 0 ≤ q1) (hξ : 0 ≤ ξ) (t : ℝ) :
    q2sel q1 ξ ≤ t ↔ (q1 ≤ t ∧ M.ratio ≤ M.F ξ t) := by
  obtain ⟨qs, hqs, hF, he⟩ := M.q2sel_eq hq2 hq1 hξ
  rw [he, max_le_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, hF ▸ M.F_mono h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_contra h; push_neg at h
    have := M.F_smono hξ (Set.mem_Ici.2 (hq1.trans h1)) (Set.mem_Ici.2 hqs.le) h
    linarith

lemma F_eq_K {ξ : ℝ} (hξ : 0 ≤ ξ) (t : ℝ) : M.F ξ t = (M.K ξ (Set.Iic t)).toReal := by
  haveI := M.isProb ξ hξ
  rw [M.K_eq hξ]; show cdf (M.D ξ) t = _
  rw [cdf_eq_real]; rfl

lemma qsel_meas {q2sel : ℝ → ℝ → ℝ} (hq2 : M.IsChainPeriod2Optimal q2sel) {q1 : ℝ}
    (hq1 : 0 ≤ q1) : Measurable (qsel q2sel q1) := by
  apply measurable_of_Iic
  intro t
  have : qsel q2sel q1 ⁻¹' Set.Iic t =
      (Set.Ici 0 ∩ {ξ | q1 ≤ t ∧ M.ratio ≤ (M.K ξ (Set.Iic t)).toReal}) ∪
        (Set.Iio 0 ∩ {_ξ | (0:ℝ) ≤ t}) := by
    ext ξ
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_inter_iff, Set.mem_Ici,
      Set.mem_Iio, Set.mem_setOf_eq, Model.qsel]
    by_cases hξ : 0 ≤ ξ
    · simp only [hξ, if_true, true_and, not_lt.2 hξ, false_and, or_false]
      rw [M.q2sel_le_iff hq2 hq1 hξ, M.F_eq_K hξ]
    · have : ξ < 0 := lt_of_not_ge hξ
      simp [hξ, this]
  rw [this]
  refine MeasurableSet.union (measurableSet_Ici.inter ?_) (measurableSet_Iio.inter ?_)
  · refine MeasurableSet.inter ?_ ?_
    · exact MeasurableSet.const _
    · exact measurableSet_le measurable_const
        ((M.K.measurable_coe measurableSet_Iic).ennreal_toReal)
  · exact MeasurableSet.const _

lemma Ssel_meas {q2sel : ℝ → ℝ → ℝ} (hq2 : M.IsChainPeriod2Optimal q2sel) {q1 : ℝ}
    (hq1 : 0 ≤ q1) : StronglyMeasurable (fun ξ => ∫ d, min (qsel q2sel q1 ξ) d ∂(M.K ξ)) := by
  have hm : StronglyMeasurable (Function.uncurry fun ξ d => min (qsel q2sel q1 ξ) d) := by
    apply Measurable.stronglyMeasurable
    exact ((M.qsel_meas hq2 hq1).comp measurable_fst).min measurable_snd
  exact hm.integral_kernel_prod_right

lemma Ssel_eq {q2sel : ℝ → ℝ → ℝ} {q1 ξ : ℝ} (hξ : 0 ≤ ξ) :
    ∫ d, min (qsel q2sel q1 ξ) d ∂(M.K ξ) = M.S ξ (q2sel q1 ξ) := by
  rw [M.K_eq hξ]; unfold Model.qsel; simp only [hξ, if_true]; rfl

lemma S_nonneg {ξ q : ℝ} (hξ : 0 ≤ ξ) (hq : 0 ≤ q) : 0 ≤ M.S ξ q := by
  show 0 ≤ ∫ d, min q d ∂(M.D ξ)
  exact integral_nonneg_of_ae (by
    filter_upwards [nv_ae_nonneg (M.D ξ) (M.nonneg ξ hξ)] with d hd
    exact le_min hq hd)

lemma S_le_mean {ξ : ℝ} (hξ : 0 ≤ ξ) (q : ℝ) : M.S ξ q ≤ ∫ x, x ∂(M.D ξ) := by
  haveI := M.isProb ξ hξ
  exact nv_sales_le_mean (M.D ξ) (M.integrable ξ hξ) q

lemma S_le {ξ : ℝ} (hξ : 0 ≤ ξ) (q : ℝ) : M.S ξ q ≤ q := by
  haveI := M.isProb ξ hξ
  show ∫ d, min q d ∂(M.D ξ) ≤ q
  calc ∫ d, min q d ∂(M.D ξ) ≤ ∫ _d, q ∂(M.D ξ) :=
        integral_mono (nv_int_min _ (M.integrable ξ hξ) q) (integrable_const q)
          (fun d => min_le_left _ _)
    _ = q := by simp

lemma mean_nonneg {ξ : ℝ} (hξ : 0 ≤ ξ) : 0 ≤ ∫ x, x ∂(M.D ξ) :=
  integral_nonneg_of_ae (nv_ae_nonneg (M.D ξ) (M.nonneg ξ hξ))

lemma aesm_of {f : ℝ → ℝ} (h : StronglyMeasurable f) {f' : ℝ → ℝ}
    (he : ∀ ξ, 0 ≤ ξ → f ξ = f' ξ) :
    AEStronglyMeasurable f' (volume.restrict (Set.Ici (0:ℝ))) :=
  h.aestronglyMeasurable.congr (ae_restrict_of_forall_mem measurableSet_Ici
    (fun ξ hξ => he ξ hξ))

lemma O2sel_int {q2sel : ℝ → ℝ → ℝ} (hq2 : M.IsChainPeriod2Optimal q2sel) {q1 : ℝ}
    (hq1 : 0 ≤ q1) :
    IntegrableOn (fun ξ => M.Omega2 q1 ξ (q2sel q1 ξ) * M.g ξ) (Set.Ici 0) := by
  have hp : 0 < M.p := M.c2_pos.trans M.c2_lt_p
  have hm : AEStronglyMeasurable (fun ξ => M.Omega2 q1 ξ (q2sel q1 ξ) * M.g ξ)
      (volume.restrict (Set.Ici (0:ℝ))) := by
    refine aesm_of (f := fun ξ => (M.p * (∫ d, min (qsel q2sel q1 ξ) d ∂(M.K ξ))
      - M.c2 * qsel q2sel q1 ξ + M.c2 * q1) * M.g ξ) ?_ ?_
    · refine StronglyMeasurable.mul ?_ M.g_measurable.stronglyMeasurable
      refine StronglyMeasurable.add (StronglyMeasurable.sub ?_ ?_) stronglyMeasurable_const
      · exact (M.Ssel_meas hq2 hq1).const_mul _
      · exact ((M.qsel_meas hq2 hq1).stronglyMeasurable).const_mul _
    · intro ξ hξ
      rw [M.Ssel_eq hξ]; unfold Model.qsel Model.Omega2; simp only [hξ, if_true]
  refine Integrable.mono' (M.mean_integrable.const_mul M.p) hm ?_
  refine ae_restrict_of_forall_mem measurableSet_Ici (fun ξ hξ => ?_)
  simp only [Set.mem_Ici] at hξ
  obtain ⟨h1, h2⟩ := hq2 q1 ξ hq1 hξ
  have hlow : M.Omega2 q1 ξ q1 ≤ M.Omega2 q1 ξ (q2sel q1 ξ) := h2 (Set.mem_Ici.2 le_rfl)
  have hO1 : M.Omega2 q1 ξ q1 = M.p * M.S ξ q1 := by unfold Model.Omega2; ring
  have hS0 := M.S_nonneg hξ hq1
  have hSm := M.S_le_mean hξ (q2sel q1 ξ)
  have hup : M.Omega2 q1 ξ (q2sel q1 ξ) ≤ M.p * ∫ x, x ∂(M.D ξ) := by
    unfold Model.Omega2; nlinarith [M.c2_pos]
  have hf0 : 0 ≤ M.Omega2 q1 ξ (q2sel q1 ξ) := by rw [hO1] at hlow; nlinarith
  have hg := M.g_nonneg ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hf0 hg)]
  have := mul_le_mul_of_nonneg_right hup hg
  linarith

end Model

namespace Model
variable (M : Model)

lemma qs_spec {q2sel : ℝ → ℝ → ℝ} (hq2 : M.IsChainPeriod2Optimal q2sel) {ξ : ℝ} (hξ : 0 ≤ ξ) :
    0 < q2sel 0 ξ ∧ M.F ξ (q2sel 0 ξ) = M.ratio ∧ ∀ q, 0 ≤ q → q2sel q ξ = max q (q2sel 0 ξ) := by
  obtain ⟨qs, hqs, hF, he⟩ := M.q2sel_eq hq2 le_rfl hξ
  rw [max_eq_right hqs.le] at he
  refine ⟨he ▸ hqs, he ▸ hF, fun q hq => ?_⟩
  obtain ⟨qs', hqs', hF', he'⟩ := M.q2sel_eq hq2 hq hξ
  rw [he', he, M.F_uniq hξ hqs'.le hqs.le hF' hF]

lemma S_lip {ξ : ℝ} (hξ : 0 ≤ ξ) (a b : ℝ) : |M.S ξ a - M.S ξ b| ≤ |a - b| := by
  haveI := M.isProb ξ hξ
  show |(∫ d, min a d ∂(M.D ξ)) - ∫ d, min b d ∂(M.D ξ)| ≤ |a - b|
  rw [← integral_sub (nv_int_min _ (M.integrable ξ hξ) a) (nv_int_min _ (M.integrable ξ hξ) b)]
  have := norm_integral_le_of_norm_le_const (μ := M.D ξ) (C := |a - b|)
    (f := fun d => min a d - min b d) (Filter.Eventually.of_forall (fun d => by
      rw [Real.norm_eq_abs]
      have := abs_min_sub_min_le_max a d b d
      simpa using this))
  simpa using this

lemma F_ge_of_le {ξ xi1 q : ℝ} (hξ : 0 ≤ ξ) (hle : ξ ≤ xi1) (hq : 0 < q) :
    M.F xi1 q ≤ M.F ξ q := by
  rcases lt_or_eq_of_le hle with h | h
  · exact (M.stoch_incr ξ xi1 q hξ h hq).le
  · rw [h]

end Model

open Model

theorem eq_27_core (M : Model) (q2sel : ℝ → ℝ → ℝ) (hq2 : M.IsChainPeriod2Optimal q2sel) :
    (∀ q1 xi1, 0 < q1 → 0 ≤ xi1 → M.F xi1 q1 = M.ratio →
      HasDerivAt (M.Omega1 q2sel)
        (-M.c1 + M.c2 * (1 - M.G xi1) +
          ∫ ξ in Set.Icc 0 xi1, M.p * (1 - M.F ξ q1) * M.g ξ) q1) ∧
    (∀ q1o xi1, 0 < q1o → IsMaxOn (M.Omega1 q2sel) (Set.Ici 0) q1o →
      0 ≤ xi1 → M.F xi1 q1o = M.ratio →
      -M.c1 + M.c2 * (1 - M.G xi1) +
          ∫ ξ in Set.Icc 0 xi1, M.p * (1 - M.F ξ q1o) * M.g ξ = 0) := by
  have hp : 0 < M.p := M.c2_pos.trans M.c2_lt_p
  have hc2 := M.c2_pos
  have part1 : ∀ q1 xi1, 0 < q1 → 0 ≤ xi1 → M.F xi1 q1 = M.ratio →
      HasDerivAt (M.Omega1 q2sel)
        (-M.c1 + M.c2 * (1 - M.G xi1) +
          ∫ ξ in Set.Icc 0 xi1, M.p * (1 - M.F ξ q1) * M.g ξ) q1 := by
    intro q1 xi1 hq1 hxi1 hF1
    set μ := volume.restrict (Set.Ici (0:ℝ)) with hμ
    let Fn : ℝ → ℝ → ℝ := fun q ξ => M.Omega2 q ξ (q2sel q ξ) * M.g ξ
    let F' : ℝ → ℝ := fun ξ => (M.c2 + min 0 (M.p * (1 - M.F ξ q1) - M.c2)) * M.g ξ
    have hs : Set.Ioi (q1 / 2) ∈ nhds q1 := Ioi_mem_nhds (by linarith)
    have hF_meas : ∀ᶠ x in nhds q1, AEStronglyMeasurable (Fn x) μ := by
      filter_upwards [Ioi_mem_nhds (show (0:ℝ) < q1 from hq1)] with x hx
      exact (M.O2sel_int hq2 (le_of_lt hx)).aestronglyMeasurable
    have hF_int : Integrable (Fn q1) μ := M.O2sel_int hq2 hq1.le
    have hF'_meas : AEStronglyMeasurable F' μ := by
      refine aesm_of (f := fun ξ => (M.c2 + min 0 (M.p * (1 - (M.K ξ (Set.Iic q1)).toReal) - M.c2))
        * M.g ξ) ?_ ?_
      · refine Measurable.stronglyMeasurable ?_
        refine Measurable.mul ?_ M.g_measurable
        refine measurable_const.add (measurable_const.min ?_)
        exact (measurable_const.mul (measurable_const.sub
          (M.K.measurable_coe measurableSet_Iic).ennreal_toReal)).sub measurable_const
      · intro ξ hξ; simp only [F']; rw [M.F_eq_K hξ]
    have h_lip : ∀ᵐ ξ ∂μ, LipschitzOnWith (Real.nnabs ((2 * M.c2 + M.p) * M.g ξ))
        (fun q => Fn q ξ) (Set.Ioi (q1 / 2)) := by
      refine ae_restrict_of_forall_mem measurableSet_Ici (fun ξ hξ => ?_)
      simp only [Set.mem_Ici] at hξ
      obtain ⟨_, _, hmax⟩ := M.qs_spec hq2 hξ
      refine LipschitzOnWith.of_dist_le_mul (fun x hx y hy => ?_)
      simp only [Set.mem_Ioi] at hx hy
      have hx0 : 0 ≤ x := by linarith
      have hy0 : 0 ≤ y := by linarith
      simp only [Fn, Real.dist_eq]
      rw [hmax x hx0, hmax y hy0]
      have hg := M.g_nonneg ξ
      have hcoe : ((Real.nnabs ((2 * M.c2 + M.p) * M.g ξ) : NNReal) : ℝ) = (2 * M.c2 + M.p) * M.g ξ := by
        rw [Real.coe_nnabs, abs_of_nonneg (by positivity)]
      rw [hcoe, ← sub_mul, abs_mul, abs_of_nonneg hg]
      have hm := abs_max_sub_max_le_abs x y (q2sel 0 ξ)
      have hS := M.S_lip hξ (max x (q2sel 0 ξ)) (max y (q2sel 0 ξ))
      have key : |M.Omega2 x ξ (max x (q2sel 0 ξ)) - M.Omega2 y ξ (max y (q2sel 0 ξ))| ≤
          (2 * M.c2 + M.p) * |x - y| := by
        unfold Model.Omega2
        have e : M.p * M.S ξ (max x (q2sel 0 ξ)) - M.c2 * max x (q2sel 0 ξ) + M.c2 * x -
            (M.p * M.S ξ (max y (q2sel 0 ξ)) - M.c2 * max y (q2sel 0 ξ) + M.c2 * y) =
            M.p * (M.S ξ (max x (q2sel 0 ξ)) - M.S ξ (max y (q2sel 0 ξ))) -
            M.c2 * (max x (q2sel 0 ξ) - max y (q2sel 0 ξ)) + M.c2 * (x - y) := by ring
        rw [e]
        calc _ ≤ |M.p * (M.S ξ (max x (q2sel 0 ξ)) - M.S ξ (max y (q2sel 0 ξ)))| +
              |M.c2 * (max x (q2sel 0 ξ) - max y (q2sel 0 ξ))| + |M.c2 * (x - y)| :=
              abs_add_three _ _ _ |>.trans (by rw [abs_neg])
          _ ≤ M.p * |x - y| + M.c2 * |x - y| + M.c2 * |x - y| := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_pos hp, abs_of_pos hc2]
              have := mul_le_mul_of_nonneg_left (hS.trans hm) hp.le
              have := mul_le_mul_of_nonneg_left hm hc2.le
              linarith
          _ = (2 * M.c2 + M.p) * |x - y| := by ring
      calc _ ≤ (2 * M.c2 + M.p) * |x - y| * M.g ξ := mul_le_mul_of_nonneg_right key hg
        _ = _ := by ring
    have h_bound : Integrable (fun ξ => (2 * M.c2 + M.p) * M.g ξ) μ :=
      M.g_integrable.const_mul _
    have hne : ∀ᵐ ξ ∂μ, ξ ≠ xi1 := by
      apply ae_restrict_of_ae
      rw [ae_iff]; simp
    have h_diff : ∀ᵐ ξ ∂μ, HasDerivAt (fun q => Fn q ξ) (F' ξ) q1 := by
      filter_upwards [hne, ae_restrict_mem measurableSet_Ici] with ξ hne' hξ
      simp only [Set.mem_Ici] at hξ
      obtain ⟨hqs, hFs, hmax⟩ := M.qs_spec hq2 hξ
      have hqne : q2sel 0 ξ ≠ q1 := by
        intro h
        rw [h] at hFs
        rcases lt_or_gt_of_ne hne' with h' | h'
        · have : M.F xi1 q1 < M.F ξ q1 := M.stoch_incr ξ xi1 q1 hξ h' hq1; linarith
        · have : M.F ξ q1 < M.F xi1 q1 := M.stoch_incr xi1 ξ q1 hxi1 h' hq1; linarith
      rcases lt_or_gt_of_ne hqne with h | h
      · -- qs < q1 : V q = p S q near q1
        have hFq : M.ratio < M.F ξ q1 := by
          rw [← hFs]; exact M.F_smono hξ (Set.mem_Ici.2 hqs.le) (Set.mem_Ici.2 hq1.le) h
        have hmin : min 0 (M.p * (1 - M.F ξ q1) - M.c2) = M.p * (1 - M.F ξ q1) - M.c2 :=
          min_eq_right ((M.deriv_neg_iff _).2 hFq).le
        have hd : HasDerivAt (fun q => M.p * M.S ξ q * M.g ξ) (F' ξ) q1 := by
          have := ((M.S_deriv hξ q1).const_mul M.p).mul_const (M.g ξ)
          refine this.congr_deriv ?_
          simp only [F']; rw [hmin]; ring
        refine hd.congr_of_eventuallyEq ?_
        filter_upwards [Ioi_mem_nhds h] with q hq
        simp only [Set.mem_Ioi] at hq
        simp only [Fn]
        rw [hmax q (hqs.le.trans hq.le), max_eq_left hq.le]
        unfold Model.Omega2; ring
      · have hFq : M.F ξ q1 < M.ratio := by
          rw [← hFs]; exact M.F_smono hξ (Set.mem_Ici.2 hq1.le) (Set.mem_Ici.2 hqs.le) h
        have hmin : min 0 (M.p * (1 - M.F ξ q1) - M.c2) = 0 :=
          min_eq_left ((M.deriv_pos_iff _).2 hFq).le
        have hd : HasDerivAt (fun q => (M.p * M.S ξ (q2sel 0 ξ) - M.c2 * q2sel 0 ξ
            + M.c2 * q) * M.g ξ) (F' ξ) q1 := by
          have := (((hasDerivAt_id q1).const_mul M.c2).const_add
            (M.p * M.S ξ (q2sel 0 ξ) - M.c2 * q2sel 0 ξ)).mul_const (M.g ξ)
          refine this.congr_deriv ?_
          simp only [F']; rw [hmin]; ring
        refine hd.congr_of_eventuallyEq ?_
        filter_upwards [Ioo_mem_nhds hq1 h] with q hq
        simp only [Fn]
        rw [hmax q hq.1.le, max_eq_right hq.2.le]
        rfl
    obtain ⟨hF'_int, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_lip hs hF_meas hF_int
      hF'_meas h_lip h_bound h_diff
    have hO : M.Omega1 q2sel = fun q => -M.c1 * q + ∫ ξ, Fn q ξ ∂μ := rfl
    rw [hO]
    have h2 := ((hasDerivAt_id q1).const_mul (-M.c1)).add hderiv
    refine h2.congr_deriv ?_
    -- compute ∫ F'
    have hF'on : IntegrableOn F' (Set.Ici 0) := hF'_int
    have hsplit : ∫ ξ, F' ξ ∂μ = (∫ ξ in Set.Icc 0 xi1, F' ξ) + ∫ ξ in Set.Ioi xi1, F' ξ := by
      rw [hμ, ← Set.Icc_union_Ioi_eq_Ici hxi1]
      exact setIntegral_union (Set.disjoint_left.2 fun a ha hb => by
          simp only [Set.mem_Icc, Set.mem_Ioi] at ha hb; linarith) measurableSet_Ioi
        (hF'on.mono_set Set.Icc_subset_Ici_self)
        (hF'on.mono_set (fun x hx => by simp only [Set.mem_Ioi] at hx; exact Set.mem_Ici.2 (by linarith)))
    have hA : ∫ ξ in Set.Icc 0 xi1, F' ξ = ∫ ξ in Set.Icc 0 xi1, M.p * (1 - M.F ξ q1) * M.g ξ := by
      refine setIntegral_congr_fun measurableSet_Icc (fun ξ hξ => ?_)
      have hle := M.F_ge_of_le hξ.1 hξ.2 hq1
      rw [hF1] at hle
      simp only [F']
      rw [min_eq_right]
      · ring
      · rcases lt_or_eq_of_le hle with h | h
        · exact ((M.deriv_neg_iff _).2 h).le
        · rw [← h]; unfold Model.ratio; field_simp; ring_nf; rfl
    have hB : ∫ ξ in Set.Ioi xi1, F' ξ = ∫ ξ in Set.Ioi xi1, M.c2 * M.g ξ := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun ξ hξ => ?_)
      simp only [Set.mem_Ioi] at hξ
      have : M.F ξ q1 < M.ratio := hF1 ▸ M.stoch_incr xi1 ξ q1 hxi1 hξ hq1
      simp only [F']
      rw [min_eq_left ((M.deriv_pos_iff _).2 this).le]; ring
    have hgsplit : (1:ℝ) = M.G xi1 + ∫ ξ in Set.Ioi xi1, M.g ξ := by
      rw [← M.g_total, ← Set.Icc_union_Ioi_eq_Ici hxi1]
      unfold Model.G
      exact setIntegral_union (Set.disjoint_left.2 fun a ha hb => by
          simp only [Set.mem_Icc, Set.mem_Ioi] at ha hb; linarith) measurableSet_Ioi
        (M.g_integrable.mono_set Set.Icc_subset_Ici_self)
        (M.g_integrable.mono_set (fun x hx => by simp only [Set.mem_Ioi] at hx; exact Set.mem_Ici.2 (by linarith)))
    simp only [F'] at hsplit hA hB
    rw [hsplit, hA, hB, integral_const_mul]
    have : ∫ ξ in Set.Ioi xi1, M.g ξ = 1 - M.G xi1 := by linarith
    rw [this]; ring
  refine ⟨part1, fun q1o xi1 hq hmax hxi1 hF => ?_⟩
  have hloc : IsLocalMax (M.Omega1 q2sel) q1o := hmax.isLocalMax (Ici_mem_nhds hq)
  exact hloc.hasDerivAt_eq_zero (part1 q1o xi1 hq hxi1 hF)

end CachonCoord.DemandUpdate

open CachonCoord.DemandUpdate


theorem solution (M : Model) (q2sel : ℝ → ℝ → ℝ) (hq2 : M.IsChainPeriod2Optimal q2sel) :
    (∀ q1 xi1, 0 < q1 → 0 ≤ xi1 → M.F xi1 q1 = M.ratio →
      HasDerivAt (M.Omega1 q2sel)
        (-M.c1 + M.c2 * (1 - M.G xi1) +
          ∫ ξ in Set.Icc 0 xi1, M.p * (1 - M.F ξ q1) * M.g ξ) q1) ∧
    (∀ q1o xi1, 0 < q1o → IsMaxOn (M.Omega1 q2sel) (Set.Ici 0) q1o →
      0 ≤ xi1 → M.F xi1 q1o = M.ratio →
      -M.c1 + M.c2 * (1 - M.G xi1) +
          ∫ ξ in Set.Icc 0 xi1, M.p * (1 - M.F ξ q1o) * M.g ξ = 0) := by
  exact eq_27_core M q2sel hq2

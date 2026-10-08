-- Prove2me | solution 1 for CachonCoord.DemandUpdate.p65_supplier_fills
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:16:20.655967+00:00
-- url     : https://prove2.me/submissions/2518bdf4-3f54-41c1-bc06-0b13372fc1f2

import Mathlib
import Definitions.Def_CachonCoord_DemandUpdate_Model
import Definitions.Def_CachonCoord_DemandUpdate_Profits

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

open Model

theorem p65_supplier_fills_core (M : Model) (lam w2 b : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hb : M.p - b = lam * M.p) (hw2 : w2 = lam * M.c2 + b) :
    (∀ x q1 ξ y, M.supplierProfit2Fill w2 b x q1 ξ y =
      (1 - lam) * (M.Omega2 q1 ξ y - M.c2 * q1) + M.c2 * x - w2 * q1) ∧
    (∀ q1 ξ x q2 qopt, 0 ≤ q1 → 0 ≤ ξ → q1 ≤ x → x < q2 →
      q1 ≤ qopt → IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) qopt → q2 ≤ qopt →
      IsMaxOn (M.supplierProfit2Fill w2 b x q1 ξ) (Set.Icc x q2) q2) ∧
    (∀ q1 ξ x q2 qopt, 0 ≤ q1 → 0 ≤ ξ → q1 ≤ x → x < q2 →
      q1 ≤ qopt → IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) qopt → lam < 1 → qopt < q2 →
      ¬ IsMaxOn (M.supplierProfit2Fill w2 b x q1 ξ) (Set.Icc x q2) q2) := by
  have hid : ∀ x q1 ξ y, M.supplierProfit2Fill w2 b x q1 ξ y =
      (1 - lam) * (M.Omega2 q1 ξ y - M.c2 * q1) + M.c2 * x - w2 * q1 := by
    intro x q1 ξ y
    have hb' : b = M.p - lam * M.p := by linarith
    unfold Model.supplierProfit2Fill Model.Omega2
    rw [hw2, hb']; ring
  refine ⟨hid, ?_, ?_⟩
  · intro q1 ξ x q2 qopt hq1 hξ hx hxq hqo hm hq2o
    obtain ⟨qs, hqs, hF⟩ := M.qstar_exists hξ
    have he := M.O2_max_uniq hξ hqs.le hF q1 qopt hqo hm
    have hqs' : qopt = qs := by
      rcases le_total q1 qs with h | h
      · rw [he, max_eq_right h]
      · rw [he, max_eq_left h] at hq2o ⊢; linarith
    intro y hy
    simp only [Set.mem_setOf_eq]
    rw [hid, hid]
    have hmono := (M.O2_smono hξ hqs.le hF q1).monotoneOn
      (Set.mem_Iic.2 (hy.2.trans (hq2o.trans hqs'.le))) (Set.mem_Iic.2 (hq2o.trans hqs'.le)) hy.2
    nlinarith
  · intro q1 ξ x q2 qopt hq1 hξ hx hxq hqo hm hl hqo2 hmax
    obtain ⟨qs, hqs, hF⟩ := M.qstar_exists hξ
    have he := M.O2_max_uniq hξ hqs.le hF q1 qopt hqo hm
    have hqs_le : qs ≤ qopt := he ▸ le_max_right _ _
    have hy : max x qopt ∈ Set.Icc x q2 := ⟨le_max_left _ _, max_le hxq.le hqo2.le⟩
    have h1 := hmax hy
    simp only [Set.mem_setOf_eq] at h1
    rw [hid, hid] at h1
    have hlt : M.Omega2 q1 ξ q2 < M.Omega2 q1 ξ (max x qopt) :=
      (M.O2_santi hξ hqs.le hF q1) (Set.mem_Ici.2 (hqs_le.trans (le_max_right _ _)))
        (Set.mem_Ici.2 (hqs_le.trans hqo2.le)) (max_lt hxq hqo2)
    nlinarith

end CachonCoord.DemandUpdate

open CachonCoord.DemandUpdate


theorem solution (M : Model) (lam w2 b : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hb : M.p - b = lam * M.p) (hw2 : w2 = lam * M.c2 + b) :
    (∀ x q1 ξ y, M.supplierProfit2Fill w2 b x q1 ξ y =
      (1 - lam) * (M.Omega2 q1 ξ y - M.c2 * q1) + M.c2 * x - w2 * q1) ∧
    (∀ q1 ξ x q2 qopt, 0 ≤ q1 → 0 ≤ ξ → q1 ≤ x → x < q2 →
      q1 ≤ qopt → IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) qopt → q2 ≤ qopt →
      IsMaxOn (M.supplierProfit2Fill w2 b x q1 ξ) (Set.Icc x q2) q2) ∧
    (∀ q1 ξ x q2 qopt, 0 ≤ q1 → 0 ≤ ξ → q1 ≤ x → x < q2 →
      q1 ≤ qopt → IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) qopt → lam < 1 → qopt < q2 →
      ¬ IsMaxOn (M.supplierProfit2Fill w2 b x q1 ξ) (Set.Icc x q2) q2) := by
  exact p65_supplier_fills_core M lam w2 b hlam0 hlam1 hb hw2

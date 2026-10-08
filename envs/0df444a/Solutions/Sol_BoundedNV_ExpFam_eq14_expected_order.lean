-- Prove2me | solution 1 for BoundedNV.ExpFam.eq14_expected_order
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T23:48:48.019282+00:00
-- url     : https://prove2.me/submissions/4af00cd1-4ff4-49f9-b825-6529dcdf224c

import Mathlib
import Definitions.Def_BoundedNV_ExpFam_Logit
import Definitions.Def_BoundedNV_ExpFam_LogPartition

open MeasureTheory Filter Set
open scoped Topology
open BoundedNV.Uniform

namespace BoundedNV.ExpFam.LocalSupport

lemma min_integrable (f : ℝ → ℝ) (hf : BoundedNV.ExpFam.IsDemandDensity f) (x : ℝ) :
    Integrable (fun t => min t x * f t) := by
  have hm : AEStronglyMeasurable (fun t : ℝ => min t x * f t) :=
    (continuous_id.min continuous_const).aestronglyMeasurable.mul hf.integrable.aestronglyMeasurable
  apply (hf.integrable.const_mul |x|).mono' hm
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf.nonneg t)]
  by_cases ht : t < 0
  · simp [hf.zero_of_neg t ht]
  · apply mul_le_mul_of_nonneg_right _ (hf.nonneg t)
    rw [abs_le]
    constructor
    · apply le_min
      · have := neg_abs_le x; have := abs_nonneg x; linarith
      · exact neg_abs_le x
    · exact (min_le_right t x).trans (le_abs_self x)

lemma min_derivative (f : ℝ → ℝ) (hf : BoundedNV.ExpFam.IsDemandDensity f) (m : ℝ) :
    HasDerivAt (expMin f) (1-demandCDF f m) m := by
  let F : ℝ → ℝ → ℝ := fun x t => min t x * f t
  let F' : ℝ → ℝ := (Ioi m).indicator f
  have hmeas : ∀ᶠ x in 𝓝 m, AEStronglyMeasurable (F x) := by
    filter_upwards [] with x
    exact (min_integrable f hf x).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable F' :=
    hf.integrable.aestronglyMeasurable.indicator measurableSet_Ioi
  have hlip : ∀ᵐ t : ℝ, LipschitzOnWith (Real.nnabs (f t)) (F · t) univ := by
    filter_upwards [] with t
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := (LipschitzWith.id.const_min t).dist_le_mul x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
    simpa only [F, Real.dist_eq, Real.coe_nnabs, ← sub_mul, ← mul_sub, abs_mul,
      id_eq, mul_comm] using
      mul_le_mul_of_nonneg_right h (abs_nonneg (f t))
  have hd : ∀ᵐ t : ℝ, HasDerivAt (F · t) (F' t) m := by
    filter_upwards [volume.ae_ne m] with t ht
    rcases lt_or_gt_of_ne ht with ht | ht
    · have he : (fun x => F x t) =ᶠ[𝓝 m] (fun _ => t*f t) := by
        filter_upwards [eventually_gt_nhds ht] with x hx
        simp [F, min_eq_left hx.le]
      have h := (hasDerivAt_const m (t*f t)).congr_of_eventuallyEq he
      simpa [F', mem_Ioi, not_lt.mpr ht.le] using h
    · have he : (fun x => F x t) =ᶠ[𝓝 m] (fun x => x*f t) := by
        filter_upwards [eventually_lt_nhds ht] with x hx
        simp [F, min_eq_right hx.le]
      have h := ((hasDerivAt_id m).mul_const (f t)).congr_of_eventuallyEq he
      simpa [F', mem_Ioi, ht] using h
  have h := (hasDerivAt_integral_of_dominated_loc_of_lip
    (bound := f) (F := F) (F' := F') (s := univ)
    (Filter.univ_mem) hmeas (min_integrable f hf m) hmeas' hlip hf.integrable hd).2
  have hi : ∫ t, F' t = 1-demandCDF f m := by
    rw [integral_indicator measurableSet_Ioi]
    have hh := integral_add_compl (s := Iic m) measurableSet_Iic hf.integrable
    rw [compl_Iic, hf.integral_eq_one] at hh
    unfold demandCDF
    linarith
  rw [hi] at h
  exact h


lemma sales_sublinear (f : ℝ → ℝ) (hf : IsDemandDensity f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, 0 ≤ x → expMin f x ≤ M + ε * x := by
  have ht : Tendsto (fun M : ℝ => ∫ t in Ioi M, f t) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero tendsto_id
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  let M := max N 0
  have hM : 0 ≤ M := le_max_right _ _
  have htail : (∫ t in Ioi M, f t) < ε := hN M (le_max_left _ _)
  refine ⟨M, hM, ?_⟩
  intro x hx
  have hi := (hf.integrable.const_mul M).add
    ((hf.integrable.indicator (s := Ioi M) measurableSet_Ioi).const_mul x)
  have hle : expMin f x ≤ ∫ t, M * f t + x * (Ioi M).indicator f t := by
    apply integral_mono (min_integrable f hf x) hi
    intro t
    change min t x * f t ≤ M * f t + x * (Ioi M).indicator f t
    by_cases ht : M < t
    · rw [indicator_of_mem (show t ∈ Ioi M from ht)]
      have h := mul_le_mul_of_nonneg_right (min_le_right t x) (hf.nonneg t)
      have h' := mul_nonneg hM (hf.nonneg t)
      linarith
    · rw [indicator_of_notMem (show t ∉ Ioi M from ht), mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_right ((min_le_left t x).trans (le_of_not_gt ht)) (hf.nonneg t)
  rw [integral_add (hf.integrable.const_mul M)
    ((hf.integrable.indicator (s := Ioi M) measurableSet_Ioi).const_mul x), integral_const_mul,
    integral_const_mul, integral_indicator measurableSet_Ioi, hf.integral_eq_one, mul_one] at hle
  exact hle.trans (by nlinarith)

lemma sales_bounds (f : ℝ → ℝ) (hf : IsDemandDensity f) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ expMin f x ∧ expMin f x ≤ x := by
  constructor
  · apply integral_nonneg
    intro t
    by_cases ht : t < 0
    · simp [hf.zero_of_neg t ht]
    · exact mul_nonneg (le_min (le_of_not_gt ht) hx) (hf.nonneg t)
  · have h := integral_mono (min_integrable f hf x) (hf.integrable.const_mul x)
      (fun t => mul_le_mul_of_nonneg_right (min_le_right t x) (hf.nonneg t))
    simpa [expMin, integral_const_mul, hf.integral_eq_one] using h

lemma domain_nonneg (f : ℝ → ℝ) (hf : IsDemandDensity f) :
    decisionDomain f ⊆ Ici 0 := by
  apply convexHull_min _ (convex_Ici 0)
  intro x hx
  by_contra hn
  exact hx (hf.zero_of_neg x (lt_of_not_ge hn))

lemma domain_measurable (f : ℝ → ℝ) : MeasurableSet (decisionDomain f) :=
  (convex_convexHull ℝ (Function.support f)).ordConnected.measurableSet

lemma exponential_moment (f : ℝ → ℝ) (hf : IsDemandDensity f)
    (a b : ℝ) (hb : 0 < b) :
    IntegrableOn (fun x => Real.exp (a * expMin f x - b * x)) (decisionDomain f) ∧
    IntegrableOn (fun x => x * Real.exp (a * expMin f x - b * x)) (decisionDomain f) := by
  obtain ⟨M, hM, hsales⟩ := sales_sublinear f hf (b / (2 * (|a|+1))) (by positivity)
  have hc : Continuous (expMin f) := continuous_iff_continuousAt.mpr
    (fun x => (min_derivative f hf x).continuousAt)
  have he : Continuous (fun x => Real.exp (a * expMin f x - b * x)) := by fun_prop
  have hb2 : 0 < b / 2 := by positivity
  have hd : ∀ x ∈ decisionDomain f,
      Real.exp (a * expMin f x - b * x) ≤ Real.exp (|a| * M) * Real.exp (-(b/2) * x) := by
    intro x hx
    have hx0 := domain_nonneg f hf hx
    have hm0 := (sales_bounds f hf x hx0).1
    have hm := hsales x hx0
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hcoef : |a| * (b / (2*(|a|+1))) ≤ b/2 := by
      apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ))).mpr
      field_simp
      nlinarith [abs_nonneg a]
    have h1 := mul_le_mul_of_nonneg_right (le_abs_self a) hm0
    have h2 := mul_le_mul_of_nonneg_left hm (abs_nonneg a)
    have h3 := mul_le_mul_of_nonneg_right hcoef hx0
    nlinarith
  have hbase : IntegrableOn (fun x : ℝ => Real.exp (-(b/2)*x)) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr (exp_neg_integrableOn_Ioi 0 hb2)
  have hmoment : IntegrableOn (fun x : ℝ => x * Real.exp (-(b/2)*x)) (Ici 0) := by
    apply (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := b/2)
        (by norm_num) (by norm_num) hb2)
  constructor
  · apply ((hbase.mono_set (domain_nonneg f hf)).const_mul (Real.exp (|a| * M))).mono' he.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (domain_measurable f)] with x hx
    simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hd x hx
  · apply ((hmoment.mono_set (domain_nonneg f hf)).const_mul (Real.exp (|a| * M))).mono'
      (continuous_id.mul he).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (domain_measurable f)] with x hx
    have hx0 := domain_nonneg f hf hx
    change 0 ≤ x at hx0
    simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx0, abs_of_pos (Real.exp_pos _), mul_assoc, mul_left_comm]
      using mul_le_mul_of_nonneg_left (hd x hx) hx0

end BoundedNV.ExpFam.LocalSupport


open MeasureTheory Filter Set
open scoped Topology
open BoundedNV.Uniform BoundedNV.ExpFam BoundedNV.ExpFam.LocalSupport
set_option maxHeartbeats 30000

namespace BoundedNV.ExpFam.LocalSupport

lemma partition_direction (f : ℝ → ℝ) (hf : IsDemandDensity f)
    (a b A B : ℝ) (hb : 0 < b) :
    HasDerivAt (fun t => ∫ x in decisionDomain f,
      Real.exp ((a + t*A) * expMin f x - (b + t*B) * x))
      (∫ x in decisionDomain f, (A * expMin f x - B*x) * Real.exp (a * expMin f x - b*x)) 0 := by
  let μ := volume.restrict (decisionDomain f)
  let K := |a| + |A| + 1
  let L := |A| + |B|
  let r := min 1 (b / (2*(|B|+1)))
  have hK : 0 < K := by dsimp [K]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  obtain ⟨M, hM, hsales⟩ := sales_sublinear f hf (b/(4*K)) (by positivity)
  let F : ℝ → ℝ → ℝ := fun t x => Real.exp ((a+t*A)*expMin f x - (b+t*B)*x)
  let F' : ℝ → ℝ → ℝ := fun t x => (A*expMin f x-B*x)*F t x
  let bound : ℝ → ℝ := fun x => L * Real.exp (K*M) * (x * Real.exp (-(b/4)*x))
  have hc : Continuous (expMin f) := continuous_iff_continuousAt.mpr
    (fun x => (min_derivative f hf x).continuousAt)
  have hmeas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) μ := by
    filter_upwards [] with t
    have : Continuous (F t) := by dsimp [F]; fun_prop
    exact this.aestronglyMeasurable
  have hi : Integrable (F 0) μ := by
    simpa [F, μ, IntegrableOn] using (exponential_moment f hf a b hb).1
  have hmeas' : AEStronglyMeasurable (F' 0) μ := by
    have : Continuous (F' 0) := by dsimp [F', F]; fun_prop
    exact this.aestronglyMeasurable
  have hib : Integrable bound μ := by
    have h := (exponential_moment f hf 0 (b/4) (by positivity)).2
    simpa [bound, μ, IntegrableOn] using h.const_mul (L * Real.exp (K*M))
  have hbound : ∀ᵐ x ∂μ, ∀ t ∈ Metric.ball 0 r, ‖F' t x‖ ≤ bound x := by
    filter_upwards [ae_restrict_mem (domain_measurable f)] with x hx
    have hx0 : 0 ≤ x := domain_nonneg f hf hx
    obtain ⟨hm0, hmx⟩ := sales_bounds f hf x hx0
    have hm := hsales x hx0
    intro t ht
    have ht0 : |t| < r := by simpa [Metric.mem_ball, Real.dist_eq] using ht
    have ht1 : |t| ≤ 1 := (le_of_lt ht0).trans (min_le_left _ _)
    have ht2 : |t| < b / (2*(|B|+1)) := lt_of_lt_of_le ht0 (min_le_right _ _)
    have hta : a+t*A ≤ K := by
      have h := abs_add_le a (t*A)
      have h' := mul_le_mul_of_nonneg_right ht1 (abs_nonneg A)
      rw [abs_mul] at h
      dsimp [K]
      linarith only [h, h', le_abs_self (a+t*A)]
    have htb : b/2 ≤ b+t*B := by
      have h : |t| * (2*(|B|+1)) < b := (lt_div_iff₀ (by positivity)).mp ht2
      have hh := neg_abs_le (t*B)
      rw [abs_mul] at hh
      nlinarith only [h, hh, abs_nonneg t]
    have hcoef : K * (b/(4*K)) = b/4 := by field_simp
    have hexp : F t x ≤ Real.exp (K*M) * Real.exp (-(b/4)*x) := by
      dsimp [F]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 := mul_le_mul_of_nonneg_right hta hm0
      have h2 := mul_le_mul_of_nonneg_left hm hK.le
      have h3 := mul_le_mul_of_nonneg_right htb hx0
      rw [mul_add, ← mul_assoc, hcoef] at h2
      linarith only [h1, h2, h3]
    have hstat : |A*expMin f x-B*x| ≤ L*x := by
      have h := abs_sub_le (A*expMin f x) 0 (B*x)
      simp only [sub_zero, zero_sub, abs_neg] at h
      rw [abs_mul, abs_mul, abs_of_nonneg hm0, abs_of_nonneg hx0] at h
      have h' := mul_le_mul_of_nonneg_left hmx (abs_nonneg A)
      dsimp [L]
      linarith only [h, h']
    have h := mul_le_mul hstat hexp (by dsimp [F]; positivity) (by dsimp [L]; positivity)
    simpa [F', bound, Real.norm_eq_abs, abs_mul, abs_of_pos (show 0 < F t x by dsimp [F]; positivity), mul_assoc, mul_left_comm] using h
  have hdiff : ∀ᵐ x ∂μ, ∀ t ∈ Metric.ball 0 r, HasDerivAt (F · x) (F' t x) t := by
    filter_upwards [] with x
    intro t ht
    have h1 := (((hasDerivAt_id t).mul_const A).const_add a).mul_const (expMin f x)
    have h2 := (((hasDerivAt_id t).mul_const B).const_add b).mul_const x
    convert (h1.sub h2).exp using 1 <;> dsimp [F, F'] <;> ring
  simpa [F, F', μ] using (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds 0 hr) hmeas hi hmeas' hbound hib hdiff).2

lemma partition_pos (f : ℝ → ℝ) (hf : IsDemandDensity f) (a b : ℝ) (hb : 0 < b) :
    0 < ∫ x in decisionDomain f, Real.exp (a * expMin f x - b*x) := by
  have hs : 0 < volume (Function.support f) :=
    (integral_pos_iff_support_of_nonneg hf.nonneg hf.integrable).mp (by rw [hf.integral_eq_one]; norm_num)
  have hS : volume (decisionDomain f) ≠ 0 := ne_of_gt
    (lt_of_lt_of_le hs (measure_mono (subset_convexHull ℝ (Function.support f))))
  letI : NeZero (volume.restrict (decisionDomain f)) := ⟨by
    intro h
    exact hS (Measure.restrict_eq_zero.mp h)⟩
  exact integral_exp_pos (exponential_moment f hf a b hb).1

lemma log_direction (f : ℝ → ℝ) (hf : IsDemandDensity f)
    (a b A B : ℝ) (hb : 0 < b) :
    HasDerivAt (fun t => logPartition f (a+t*A) (b+t*B))
      ((∫ x in decisionDomain f, (A*expMin f x-B*x)*Real.exp (a*expMin f x-b*x)) /
        (∫ x in decisionDomain f, Real.exp (a*expMin f x-b*x))) 0 := by
  have h := (partition_direction f hf a b A B hb).log
    (by simpa using (partition_pos f hf a b hb).ne')
  simpa [logPartition] using h

lemma logit_ratio (f : ℝ → ℝ) (p c β : ℝ) (g : ℝ → ℝ) :
    logitExp (decisionDomain f) (nvProfit f p c) β g =
      (∫ x in decisionDomain f, g x * Real.exp ((p/β)*expMin f x-(c/β)*x)) /
        (∫ x in decisionDomain f, Real.exp ((p/β)*expMin f x-(c/β)*x)) := by
  have hexp : (fun x => Real.exp (nvProfit f p c x / β)) =
      (fun x => Real.exp ((p/β)*expMin f x-(c/β)*x)) := by
    ext x
    congr 1
    dsimp [nvProfit]
    ring
  unfold logitExp logitDensity
  rw [hexp]
  simp_rw [← Set.indicator_mul_right, ← mul_div_assoc]
  rw [integral_indicator (domain_measurable f), integral_div]
  simp_rw [show ∀ x, Real.exp (nvProfit f p c x / β) =
    Real.exp ((p/β)*expMin f x-(c/β)*x) from fun x => congrFun hexp x]

end BoundedNV.ExpFam.LocalSupport

open MeasureTheory
open BoundedNV.ExpFam BoundedNV.ExpFam.LocalSupport

theorem solution (f : ℝ → ℝ) (hf : IsDemandDensity f)
    (p c β : ℝ) (hβ : 0 < β) (hc : 0 < c) (hcp : c < p) :
    HasDerivAt (fun t => logPartition f (p / β) t)
      (-(BoundedNV.Uniform.logitExp (decisionDomain f) (BoundedNV.Uniform.nvProfit f p c) β id)) (c / β) := by
  have h := (log_direction f hf (p/β) (c/β) 0 1 (div_pos hc hβ)).comp_of_eq (c/β)
    ((hasDerivAt_id (c/β)).sub_const (c/β)) (by simp)
  rw [logit_ratio]
  simpa [Function.comp_def, integral_neg, neg_mul, neg_div] using h

#print axioms solution

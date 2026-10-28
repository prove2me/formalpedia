-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_hasWeakDerivAlong_of_sq_difference_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:34:39.426094+00:00
-- url     : https://prove2.me/submissions/78a9594c-520d-460c-b6a3-eecae8f44997

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Mollification
import Theorems.Thm_FunctionalInequalities_Analysis_quotient_pairing_tendsto_readable

noncomputable section
open MeasureTheory
open scoped ContDiff
section LN11C1WeakDerivativeOfDifferenceBound
open MeasureTheory Set Filter
open scoped Topology
section MeasurableSpace
variable {X : Type*}
variable [MeasurableSpace X]
private lemma FunctionalInequalities.Analysis.l2_pairing_toLp
    {μ : Measure X} (A : Lp ℝ 2 μ) {b : X → ℝ} (hb : MemLp b 2 μ) :
    inner ℝ A (hb.toLp b) = ∫ x, A x * b x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hb.coeFn_toLp] with x hx
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, hx]
  exact mul_comm _ _
private lemma FunctionalInequalities.Analysis.l2_toLp_norm_sq
    {μ : Measure X} {a : X → ℝ} (ha : MemLp a 2 μ) :
    ‖ha.toLp a‖ ^ 2 = ∫ x, a x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, l2_pairing_toLp]
  apply integral_congr_ae
  filter_upwards [ha.coeFn_toLp] with x hx
  rw [hx, pow_two]
end MeasurableSpace
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
variable [BorelSpace E]
private lemma FunctionalInequalities.Analysis.translated_memLp {f : E → ℝ}
    (hf : MemLp f 2 (volume : Measure E)) (w : E) :
    MemLp (fun x => f (x - w)) 2 (volume : Measure E) := by
  simpa only [Function.comp_def, sub_eq_add_neg] using
    hf.comp_measurePreserving (measurePreserving_add_right volume (-w))
/-- **Difference-quotient criterion for a weak derivative in `L²`** (Nirenberg; Evans PDE §5.8.2 Thm 3(ii); weak Letwin
route): if `f ∈ L²` and `∫ (f(x + t v) − f(x))² ≤ C t²` for all small `t ≠ 0`, then `f` has a weak
derivative along `v` that lies in `L²`. -/
theorem solution
    {f : E → ℝ} (hf : MemLp f 2 (volume : Measure E)) (v : E) {C : ℝ}
    (hdiff : ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 →
      ∫ x, (f (x + t • v) - f x) ^ 2 ∂(volume : Measure E) ≤ C * t ^ 2) :
    ∃ g : E → ℝ, FunctionalInequalities.Analysis.HasWeakDerivAlong f g v ∧ MemLp g 2 (volume : Measure E) := by
  have hC : 0 ≤ C := by
    have h := hdiff 1 one_ne_zero (by norm_num)
    have hn : 0 ≤ ∫ x, (f (x + (1 : ℝ) • v) - f x) ^ 2 :=
      integral_nonneg (fun x => sq_nonneg _)
    norm_num only [one_pow, mul_one] at h
    exact hn.trans h
  let Q : ℝ → E → ℝ := fun t x => t⁻¹ * (f (x - t • v) - f x)
  have hQ (t : ℝ) : MemLp (Q t) 2 (volume : Measure E) :=
    ((FunctionalInequalities.Analysis.translated_memLp hf (t • v)).sub hf).const_mul t⁻¹
  let A : ℝ → Lp ℝ 2 (volume : Measure E) := fun t => (hQ t).toLp (Q t)
  have hbound (t : ℝ) (ht : t ≠ 0) (ht1 : |t| ≤ 1) :
      ‖A t‖ ≤ Real.sqrt C := by
    apply (Real.le_sqrt (norm_nonneg _) hC).2
    have hdiff' :
        (∫ x, (f (x - t • v) - f x) ^ 2) ≤ C * t ^ 2 := by
      simpa only [neg_smul, sub_eq_add_neg, neg_sq] using
        hdiff (-t) (neg_ne_zero.mpr ht) (by simpa only [abs_neg] using ht1)
    calc
      ‖A t‖ ^ 2 = ∫ x, (Q t x) ^ 2 := FunctionalInequalities.Analysis.l2_toLp_norm_sq (hQ t)
      _ = t⁻¹ ^ 2 * ∫ x, (f (x - t • v) - f x) ^ 2 := by
        simp only [Q, mul_pow, integral_const_mul]
      _ ≤ t⁻¹ ^ 2 * (C * t ^ 2) :=
        mul_le_mul_of_nonneg_left hdiff' (sq_nonneg _)
      _ = C := by field_simp
  let W : ℝ → WeakDual ℝ (Lp ℝ 2 (volume : Measure E)) := fun t =>
    (InnerProductSpace.toDual ℝ (Lp ℝ 2 (volume : Measure E)) (A t)).toWeakDual
  have hevent :
      ∀ᶠ t in 𝓝[≠] (0 : ℝ),
        W t ∈ WeakDual.toStrongDual ⁻¹'
          Metric.closedBall (0 : StrongDual ℝ (Lp ℝ 2 (volume : Measure E)))
            (Real.sqrt C) := by
    filter_upwards [eventually_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)]
      with t ht ht1
    have ht0 : t ≠ 0 := ht
    have ht2 : |t| ≤ 1 := by
      exact (show |t| < 1 from by
        simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using ht1).le
    change dist (InnerProductSpace.toDual ℝ (Lp ℝ 2 (volume : Measure E)) (A t)) 0
      ≤ Real.sqrt C
    simpa only [dist_zero_right, LinearIsometryEquiv.norm_map] using hbound t ht0 ht2
  obtain ⟨L, _, hL⟩ :=
    (WeakDual.isCompact_closedBall
      (0 : StrongDual ℝ (Lp ℝ 2 (volume : Measure E))) (Real.sqrt C)).exists_mapClusterPt
      (u := W) (f := 𝓝[≠] (0 : ℝ)) (le_principal_iff.mpr hevent)
  let G : Lp ℝ 2 (volume : Measure E) :=
    (InnerProductSpace.toDual ℝ (Lp ℝ 2 (volume : Measure E))).symm L.toStrongDual
  have hg : MemLp (fun x => -(G x)) 2 (volume : Measure E) := (Lp.memLp G).neg
  refine ⟨fun x => -(G x), ⟨hf.locallyIntegrable (by norm_num),
    hg.locallyIntegrable (by norm_num), ?_⟩, hg⟩
  intro ψ hψ hψc
  have hp : MemLp ψ 2 (volume : Measure E) :=
    hψ.continuous.memLp_of_hasCompactSupport hψc
  let P : Lp ℝ 2 (volume : Measure E) := hp.toLp ψ
  have heq (t : ℝ) : W t P = ∫ x, Q t x * ψ x := by
    change inner ℝ (A t) P = _
    rw [FunctionalInequalities.Analysis.l2_pairing_toLp]
    apply integral_congr_ae
    filter_upwards [(hQ t).coeFn_toLp] with x hx
    rw [hx]
  have ht : Tendsto (fun t => W t P) (𝓝[≠] (0 : ℝ))
      (𝓝 (∫ x, f x * fderiv ℝ ψ x v)) := by
    exact (FunctionalInequalities.Analysis.quotient_pairing_tendsto_readable hf v hψ hψc).congr'
      (.of_forall fun t => (heq t).symm)
  have hc : MapClusterPt (L P) (𝓝[≠] (0 : ℝ)) (fun t => W t P) :=
    MapClusterPt.continuousAt_comp (WeakDual.eval_continuous P).continuousAt hL
  have hvalue : L P = ∫ x, f x * fderiv ℝ ψ x v :=
    eq_of_nhds_neBot (hc.clusterPt.mono ht).neBot
  have hrepr : (∫ x, G x * ψ x) = L P := by
    rw [← FunctionalInequalities.Analysis.l2_pairing_toLp G hp]
    exact InnerProductSpace.toDual_symm_apply
  calc
    (∫ x, f x * fderiv ℝ ψ x v) = ∫ x, G x * ψ x :=
      hvalue.symm.trans hrepr.symm
    _ = -(∫ x, (-(G x)) * ψ x) := by
      simp only [neg_mul, integral_neg, neg_neg]

-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Mollification.tendsto_eLpNorm_convolution_sub_of_continuous_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:27:29.126435+00:00
-- url     : https://prove2.me/submissions/81543db1-0279-4bc8-b9a9-74d860494fdb

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Mollification_Basic

noncomputable section
open MeasureTheory Filter Topology Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace
open FunctionalInequalities.Analysis.BakryEmery
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {m : MeasureTheory.Measure V} [m.IsAddHaarMeasure]
section Convergence
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
omit [CompleteSpace E] in
/-- The support of a mollification with `rOut ≤ ε` lies in the closed `ε`-thickening of the
support of the function. -/
theorem FunctionalInequalities.Analysis.Mollification.support_convolution_subset_cthickening_of_rOut_le (φ : ContDiffBump (0 : V)) {ε : ℝ}
    (hφ : φ.rOut ≤ ε) (f : V → E) :
    Function.support (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) ⊆
      cthickening ε (tsupport f) := by
  refine (support_convolution_subset _).trans ?_
  rintro x ⟨a, ha, b, hb, rfl⟩
  rw [φ.support_normed_eq] at ha
  refine mem_cthickening_of_dist_le (a + b) b ε _ (subset_tsupport _ hb) ?_
  rw [dist_eq_norm, add_sub_cancel_right]
  rw [mem_ball, dist_zero_right] at ha
  exact ha.le.trans hφ
omit [CompleteSpace E] in
/-- The support of a mollification with `rOut ≤ 1` lies in the closed `1`-thickening of the
support of the function. -/
theorem FunctionalInequalities.Analysis.Mollification.support_convolution_subset_cthickening (φ : ContDiffBump (0 : V)) (hφ : φ.rOut ≤ 1)
    (f : V → E) :
    Function.support (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) ⊆
      cthickening 1 (tsupport f) :=
  support_convolution_subset_cthickening_of_rOut_le φ hφ f
/-- **Mollifications of a continuous compactly supported function converge in `L²`** as the
radius of the bump tends to zero. -/
theorem solution {φ : ℕ → ContDiffBump (0 : V)}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) {f : V → E} (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    Tendsto (fun n => eLpNorm ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f - f) 2 m)
      atTop (𝓝 0) := by
  set K : Set V := cthickening 1 (tsupport f) with hK
  have hKc : IsCompact K := hfc.cthickening
  have hKfin : m K ≠ ⊤ := hKc.measure_lt_top.ne
  set c : ℝ≥0∞ := m K ^ (2 : ℝ≥0∞).toReal⁻¹ with hc
  have hcfin : c ≠ ⊤ := by
    rw [hc]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hKfin
  have hunif : UniformContinuous f := hfc.uniformContinuous_of_continuous hf
  have hev1 : ∀ᶠ n in atTop, (φ n).rOut ≤ 1 :=
    hφ.eventually (ge_mem_nhds zero_lt_one)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  -- a real bound `δ > 0` with `c * ofReal δ ≤ ε`
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ c * ENNReal.ofReal δ ≤ ε := by
    by_cases hc0 : c = 0
    · exact ⟨1, one_pos, by rw [hc0, zero_mul]; exact bot_le⟩
    by_cases hεtop : ε = ⊤
    · exact ⟨1, one_pos, by rw [hεtop]; exact le_top⟩
    have hdiv : ε / c ≠ ⊤ := ENNReal.div_ne_top hεtop hc0
    refine ⟨(ε / c).toReal, ENNReal.toReal_pos (ENNReal.div_pos hε.ne' hcfin).ne' hdiv, ?_⟩
    rw [ENNReal.ofReal_toReal hdiv, ENNReal.mul_div_cancel hc0 hcfin]
  obtain ⟨η, hη, hηδ⟩ := Metric.uniformContinuous_iff.mp hunif δ hδ
  have hev2 : ∀ᶠ n in atTop, (φ n).rOut < η := hφ.eventually (gt_mem_nhds hη)
  filter_upwards [hev1, hev2] with n hn1 hn2
  have hbound : ∀ x, ‖((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f - f) x‖ ≤ δ := by
    intro x
    rw [Pi.sub_apply, ← dist_eq_norm]
    refine ContDiffBump.dist_normed_convolution_le hf.aestronglyMeasurable fun y hy => ?_
    rw [mem_ball] at hy
    exact (hηδ (lt_of_lt_of_le hy hn2.le)).le
  have hsupp : Function.support ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f - f) ⊆ K := by
    refine (Function.support_sub _ _).trans (Set.union_subset ?_ ?_)
    · exact FunctionalInequalities.Analysis.Mollification.support_convolution_subset_cthickening (φ n) hn1 f
    · exact (subset_tsupport f).trans (self_subset_cthickening _)
  calc eLpNorm ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f - f) 2 m
      = eLpNorm ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f - f) 2 (m.restrict K) :=
        (eLpNorm_restrict_eq_of_support_subset hsupp).symm
    _ ≤ (m.restrict K) Set.univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal δ :=
        eLpNorm_le_of_ae_bound (Filter.Eventually.of_forall hbound)
    _ = c * ENNReal.ofReal δ := by rw [Measure.restrict_apply_univ]
    _ ≤ ε := hδε

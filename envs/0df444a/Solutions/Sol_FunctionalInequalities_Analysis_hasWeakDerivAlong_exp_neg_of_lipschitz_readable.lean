-- Prove2me | solution 1 for FunctionalInequalities.Analysis.hasWeakDerivAlong_exp_neg_of_lipschitz_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:39:22.093932+00:00
-- url     : https://prove2.me/submissions/7e3bdd31-d19d-46ec-a308-898d6f7af342

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_of_lipschitz_readable

noncomputable section
open MeasureTheory
open scoped ContDiff
universe u
section WeakNegativeExponential
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology
section StructuredSpace
variable {E : Type*}
variable [NormedAddCommGroup E]
section NormedSpace
variable [NormedSpace ℝ E]
private lemma FunctionalInequalities.Analysis.weak_measurable_fderiv_apply
    [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (v : E) :
    Measurable (fun x => fderiv ℝ f x v) :=
  (ContinuousLinearMap.apply ℝ ℝ v).measurable.comp (measurable_fderiv ℝ f)
private lemma FunctionalInequalities.Analysis.weak_norm_fderiv_apply_le
    {f : E → ℝ} {L : NNReal} (hf : LipschitzWith L f) (v x : E) :
    ‖fderiv ℝ f x v‖ ≤ (L : ℝ) * ‖v‖ :=
  (fderiv ℝ f x).le_opNorm v |>.trans
    (mul_le_mul_of_nonneg_right
      (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg v))
private lemma FunctionalInequalities.Analysis.weak_fderiv_apply_eq_zero_off_tsupport
    {f : E → ℝ} {x : E} (hx : x ∉ tsupport f) (v : E) :
    fderiv ℝ f x v = 0 := by
  have hz : fderiv ℝ f x = 0 :=
    image_eq_zero_of_notMem_tsupport
      (fun h => hx ((tsupport_fderiv_subset ℝ) h))
  rw [hz]
  rfl
end NormedSpace
private lemma FunctionalInequalities.Analysis.weak_exists_compact_contDiff_eq_one_near [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsCompact K) :
    ∃ χ : E → ℝ, ContDiff ℝ 1 χ ∧ HasCompactSupport χ ∧
      ∀ x ∈ K, χ =ᶠ[𝓝 x] (fun _ => 1) := by
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : E)
  let φ : ContDiffBump (0 : E) :=
    ⟨max r 0 + 1, max r 0 + 2, by positivity, by linarith⟩
  refine ⟨φ, φ.contDiff, φ.hasCompactSupport, ?_⟩
  intro x hx
  apply φ.eventuallyEq_one_of_mem_ball
  have h := hr hx
  change dist x 0 ≤ r at h
  change dist x 0 < max r 0 + 1
  linarith [le_max_left r 0]
end StructuredSpace
/-- A globally Lipschitz exponent has a local weak negative exponential
with its explicit chain density in L2 on compact sets. No bound on the
exponent or its exponential, and no C1 regularity of F, is assumed. -/
theorem solution {E : Type u}
    [instNormedAddCommGroup : NormedAddCommGroup E]
    [instInnerProductSpace : InnerProductSpace ℝ E]
    [instFiniteDimensional : FiniteDimensional ℝ E]
    [instMeasurableSpace : MeasurableSpace E] [instBorelSpace : BorelSpace E]
    {F : E → ℝ} {L : NNReal} (hF : LipschitzWith L F) (v : E) :
    FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => Real.exp (-F x))
      (fun x => -Real.exp (-F x) * fderiv ℝ F x v) v ∧
    ∀ S : Set E, IsCompact S →
      MemLp (fun x => -Real.exp (-F x) * fderiv ℝ F x v) 2
        ((volume : Measure E).restrict S) := by
  have hexp : Continuous (fun x => Real.exp (-F x)) :=
    Real.continuous_exp.comp hF.continuous.neg
  have hweakF := FunctionalInequalities.Analysis.hasWeakDerivAlong_of_lipschitz_readable hF v
  have hchain :
      ∀ᵐ x : E ∂(volume : Measure E),
        fderiv ℝ (fun y => Real.exp (-F y)) x v =
          -Real.exp (-F x) * fderiv ℝ F x v := by
    filter_upwards [hF.ae_differentiableAt] with x hx
    have hd :
        fderiv ℝ (fun y => Real.exp (-F y)) x =
          Real.exp (-F x) • (-fderiv ℝ F x) :=
      hx.hasFDerivAt.neg.exp.fderiv
    rw [hd]
    change Real.exp (-F x) * (-(fderiv ℝ F x v)) =
      -Real.exp (-F x) * fderiv ℝ F x v
    ring
  constructor
  · refine ⟨hexp.locallyIntegrable,
      LocallyIntegrable.continuous_mul hexp.neg hweakF.2.1, ?_⟩
    intro ψ hψ hψc
    obtain ⟨χ, hχ, hχc, hχone⟩ :=
      FunctionalInequalities.Analysis.weak_exists_compact_contDiff_eq_one_near (hψc.isCompact.image hF.continuous)
    let q : ℝ → ℝ := fun t => χ t * Real.exp (-t)
    have hq : ContDiff ℝ 1 q :=
      hχ.mul (contDiff_id.neg.exp)
    have hqc : HasCompactSupport q := hχc.mul_right
    obtain ⟨C, hqLip⟩ :=
      ContDiff.lipschitzWith_of_hasCompactSupport hqc hq (by simp)
    have hweakq :
        FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => q (F x))
          (fun x => fderiv ℝ (fun y => q (F y)) x v) v :=
      FunctionalInequalities.Analysis.hasWeakDerivAlong_of_lipschitz_readable (hqLip.comp hF) v
    have heq : ∀ x ∈ tsupport ψ,
        (fun y => q (F y)) =ᶠ[𝓝 x] (fun y => Real.exp (-F y)) := by
      intro x hx
      have hone :=
        (hχone (F x) ⟨x, hx, rfl⟩).comp_tendsto hF.continuous.continuousAt
      filter_upwards [hone] with y hy
      change χ (F y) = 1 at hy
      change χ (F y) * Real.exp (-F y) = Real.exp (-F y)
      rw [hy, one_mul]
    have hleft :
        (∫ x, Real.exp (-F x) * fderiv ℝ ψ x v ∂(volume : Measure E)) =
          ∫ x, q (F x) * fderiv ℝ ψ x v ∂(volume : Measure E) := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ tsupport ψ
      · rw [(heq x hx).eq_of_nhds]
      · rw [FunctionalInequalities.Analysis.weak_fderiv_apply_eq_zero_off_tsupport hx v, mul_zero, mul_zero]
    have hright :
        (∫ x, fderiv ℝ (fun y => q (F y)) x v * ψ x ∂(volume : Measure E)) =
          ∫ x, (-Real.exp (-F x) * fderiv ℝ F x v) * ψ x
            ∂(volume : Measure E) := by
      apply integral_congr_ae
      filter_upwards [hchain] with x hxchain
      by_cases hx : x ∈ tsupport ψ
      · rw [(heq x hx).fderiv_eq, hxchain]
      · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]
    calc
      (∫ x, Real.exp (-F x) * fderiv ℝ ψ x v ∂(volume : Measure E)) =
          ∫ x, q (F x) * fderiv ℝ ψ x v ∂(volume : Measure E) := hleft
      _ = -(∫ x, fderiv ℝ (fun y => q (F y)) x v * ψ x
          ∂(volume : Measure E)) := hweakq.2.2 ψ hψ hψc
      _ = -(∫ x, (-Real.exp (-F x) * fderiv ℝ F x v) * ψ x
          ∂(volume : Measure E)) := congrArg Neg.neg hright
  · intro S hS
    let : IsFiniteMeasure ((volume : Measure E).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hexp.continuousOn
    apply MemLp.of_bound
      (hexp.neg.measurable.mul (FunctionalInequalities.Analysis.weak_measurable_fderiv_apply F v)).aestronglyMeasurable
      (C * ((L : ℝ) * ‖v‖))
    filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
    calc
      ‖-Real.exp (-F x) * fderiv ℝ F x v‖ =
          ‖Real.exp (-F x)‖ * ‖fderiv ℝ F x v‖ := by
        rw [norm_mul, norm_neg]
      _ ≤ ‖Real.exp (-F x)‖ * ((L : ℝ) * ‖v‖) :=
        mul_le_mul_of_nonneg_left (FunctionalInequalities.Analysis.weak_norm_fderiv_apply_le hF v x) (norm_nonneg _)
      _ ≤ C * ((L : ℝ) * ‖v‖) :=
        mul_le_mul_of_nonneg_right (hC x hx)
          (mul_nonneg L.coe_nonneg (norm_nonneg v))

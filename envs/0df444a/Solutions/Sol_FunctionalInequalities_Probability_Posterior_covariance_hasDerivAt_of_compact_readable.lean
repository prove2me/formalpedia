-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.covariance_hasDerivAt_of_compact_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:28:18.757766+00:00
-- url     : https://prove2.me/submissions/a355e696-443c-47ab-a874-790383624825

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactPrior
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_expectation_hasDerivAt_of_compact_readable

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [SecondCountableTopology Ω]
/-- A measurable statistic bounded on the support is in `L²` of the tilt. -/
theorem FunctionalInequalities.Probability.Posterior.memLp_two_tilted_of_compact (μ : ProbabilityMeasure Ω) (hc : IsCompact (μ : Measure Ω).support)
    {φ f : Ω → ℝ} (hφ : Continuous φ) (hf : Measurable f) {C : ℝ}
    (hb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
    MemLp f 2 ((μ : Measure Ω).tilted φ) := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
  apply (integrable_tilted_iff (integrable_exp_of_compact μ hc hφ) (fun x => f x ^ 2)).mpr
  have hd : Integrable (fun x => Real.exp (φ x) * f x ^ 2) (μ : Measure Ω) := by
    apply integrable_exp_mul_of_compact μ hc hφ (hf.pow_const 2) (C := C ^ 2) (sq_nonneg C)
    intro x hx
    rw [norm_pow]
    have hB : 0 ≤ C := (norm_nonneg (f x)).trans (hb x hx)
    exact (sq_le_sq₀ (norm_nonneg _) hB).mpr (hb x hx)
  simpa only [smul_eq_mul] using hd
omit [BorelSpace Ω] [SecondCountableTopology Ω] in
private theorem FunctionalInequalities.Probability.Posterior.bound_mul {μ : ProbabilityMeasure Ω} {f k : Ω → ℝ} {C D : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C)
    (hk : ∀ x ∈ (μ : Measure Ω).support, ‖k x‖ ≤ D) :
    ∀ x ∈ (μ : Measure Ω).support, ‖f x * k x‖ ≤ C * D := by
  intro x hx
  rw [norm_mul]
  exact mul_le_mul (hf x hx) (hk x hx) (norm_nonneg _) hC
/-- **Derivative of a tilted covariance under a compact prior**: for continuous `φ, g, k` and measurable `f`
bounded on the support, `t ↦ Cov_{μ.tilted(φ + t g)}(f, k)` has derivative
`Cov(f, g k) − (∫ g) Cov(f, k) − (∫ k) Cov(f, g)` (all under `μ.tilted φ`) at `t = 0`. -/
theorem solution (μ : ProbabilityMeasure Ω)
    (hc : IsCompact (μ : Measure Ω).support) {φ g k f : Ω → ℝ}
    (hφ : Continuous φ) (hg : Continuous g) (hk : Continuous k) (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
    HasDerivAt (fun t : ℝ => covariance f k
      ((μ : Measure Ω).tilted (fun x => φ x + t * g x)))
      (covariance f (fun x => g x * k x) ((μ : Measure Ω).tilted φ) -
        (∫ x, g x ∂((μ : Measure Ω).tilted φ)) * covariance f k ((μ : Measure Ω).tilted φ) -
        (∫ x, k x ∂((μ : Measure Ω).tilted φ)) * covariance f g ((μ : Measure Ω).tilted φ)) 0 := by
  obtain ⟨D, hD, hkb⟩ := FunctionalInequalities.Probability.Posterior.exists_bound_on_support_of_compact μ hc hk
  obtain ⟨G, hG, hgb⟩ := FunctionalInequalities.Probability.Posterior.exists_bound_on_support_of_compact μ hc hg
  have hfk := FunctionalInequalities.Probability.Posterior.bound_mul hC hfb hkb
  have hgk := FunctionalInequalities.Probability.Posterior.bound_mul hG hgb hkb
  have hN := FunctionalInequalities.Probability.Posterior.expectation_hasDerivAt_of_compact_readable μ hc hφ hg
    (hf.mul hk.measurable) (mul_nonneg hC hD) hfk
  have hF := FunctionalInequalities.Probability.Posterior.expectation_hasDerivAt_of_compact_readable μ hc hφ hg hf hC hfb
  have hK := FunctionalInequalities.Probability.Posterior.expectation_hasDerivAt_of_compact_readable μ hc hφ hg hk.measurable hD hkb
  have hfun : (fun t : ℝ => covariance f k ((μ : Measure Ω).tilted (fun x => φ x + t * g x))) =
      fun t => (∫ x, f x * k x ∂((μ : Measure Ω).tilted (fun x => φ x + t * g x))) -
        (∫ x, f x ∂((μ : Measure Ω).tilted (fun x => φ x + t * g x))) *
        (∫ x, k x ∂((μ : Measure Ω).tilted (fun x => φ x + t * g x))) := by
    funext t
    have hp : Continuous (fun x => φ x + t * g x) := hφ.add (hg.const_mul t)
    let : IsProbabilityMeasure ((μ : Measure Ω).tilted (fun x => φ x + t * g x)) :=
      FunctionalInequalities.Probability.Posterior.isProbabilityMeasure_tilted_of_compact μ hc hp
    rw [covariance_eq_sub (FunctionalInequalities.Probability.Posterior.memLp_two_tilted_of_compact μ hc hp hf hfb)
      (FunctionalInequalities.Probability.Posterior.memLp_two_tilted_of_compact μ hc hp hk.measurable hkb)]
    rfl
  let ν : Measure Ω := (μ : Measure Ω).tilted φ
  let : IsProbabilityMeasure ν := FunctionalInequalities.Probability.Posterior.isProbabilityMeasure_tilted_of_compact μ hc hφ
  have hF2 : MemLp f 2 ν := FunctionalInequalities.Probability.Posterior.memLp_two_tilted_of_compact μ hc hφ hf hfb
  have hK2 : MemLp k 2 ν := FunctionalInequalities.Probability.Posterior.memLp_two_tilted_of_compact μ hc hφ hk.measurable hkb
  have hG2 : MemLp g 2 ν := FunctionalInequalities.Probability.Posterior.memLp_two_tilted_of_compact μ hc hφ hg.measurable hgb
  have hFK2 : MemLp (fun x => f x * k x) 2 ν :=
    FunctionalInequalities.Probability.Posterior.memLp_two_tilted_of_compact μ hc hφ (hf.mul hk.measurable) hfk
  have hGK2 : MemLp (fun x => g x * k x) 2 ν :=
    FunctionalInequalities.Probability.Posterior.memLp_two_tilted_of_compact μ hc hφ (hg.mul hk).measurable hgk
  have hrate : covariance (fun x => f x * k x) g ν -
      (covariance f g ν * ∫ x, k x ∂ν + (∫ x, f x ∂ν) * covariance k g ν) =
      covariance f (fun x => g x * k x) ν -
        (∫ x, g x ∂ν) * covariance f k ν - (∫ x, k x ∂ν) * covariance f g ν := by
    rw [covariance_eq_sub hFK2 hG2, covariance_eq_sub hF2 hG2,
      covariance_eq_sub hK2 hG2, covariance_eq_sub hF2 hGK2, covariance_eq_sub hF2 hK2]
    simp only [Pi.mul_apply]
    have hfgk : (fun x => f x * k x * g x) = fun x => f x * (g x * k x) := by funext x; ring
    have hkg : (fun x => k x * g x) = fun x => g x * k x := by funext x; ring
    rw [hfgk, hkg]
    ring
  rw [hfun]
  have hd := hN.sub (hF.mul hK)
  simp only [zero_mul, add_zero] at hd
  change covariance (f * k) g ((μ : Measure Ω).tilted φ) -
      (covariance f g ((μ : Measure Ω).tilted φ) * (∫ x, k x ∂((μ : Measure Ω).tilted φ)) +
        (∫ x, f x ∂((μ : Measure Ω).tilted φ)) * covariance k g ((μ : Measure Ω).tilted φ)) = _ at hrate
  rw [hrate] at hd
  convert! hd using 1

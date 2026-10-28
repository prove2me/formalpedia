-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.fderiv_logPartition_c_apply_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:33:39.465931+00:00
-- url     : https://prove2.me/submissions/00e53840-eede-4e5f-ba45-c3738993b301

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_Exponent
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_Generator
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_LogPartition
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_weighted_integral_quadraticExponent_of_compact_readable
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_exists_uniform_norm_moments_tilted_quadraticExponent_of_compact_readable
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_hasDerivAt_weighted_integral_of_compact_readable

section
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- A tilted expectation as the ratio of prior integrals. -/
theorem FunctionalInequalities.Probability.Posterior.integral_tilted_eq_div {Ω : Type*} [MeasurableSpace Ω] (μ : ProbabilityMeasure Ω)
    (φ f : Ω → ℝ) :
    (∫ x, f x ∂((μ : Measure Ω).tilted φ)) =
      (∫ x, Real.exp (φ x) * f x ∂(μ : Measure Ω)) / ∫ x, Real.exp (φ x) ∂(μ : Measure Ω) := by
  rw [integral_tilted]
  simp only [smul_eq_mul, div_mul_eq_mul_div]
  exact integral_div _ _
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section Mean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- `∫ ⟪h, x⟫ dμ_{c,Q} = ⟪h, a⟫` (finite second moment from compact support). -/
theorem FunctionalInequalities.Probability.Posterior.integral_inner_eq_inner_posteriorMean (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) (h : E) :
    (∫ x, ⟪h, x⟫ ∂((μ : Measure E).tilted (quadraticExponent c Q))) = ⟪h, posteriorMean μ c Q⟫ := by
  obtain ⟨R, _hR, hmom⟩ := exists_uniform_norm_moments_tilted_quadraticExponent_of_compact_readable μ hc
  let : IsProbabilityMeasure ((μ : Measure E).tilted (quadraticExponent c Q)) := isProbabilityMeasure_tilted_quadraticExponent_of_compact μ hc c Q
  have h2 : MemLp id 2 ((μ : Measure E).tilted (quadraticExponent c Q)) :=
    (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).mpr (hmom c Q 2).1
  have hi := h2.integrable one_le_two
  change (∫ x, (innerSL ℝ h) (id x) ∂((μ : Measure E).tilted (quadraticExponent c Q))) =
    (innerSL ℝ h) (∫ x, id x ∂((μ : Measure E).tilted (quadraticExponent c Q)))
  exact (innerSL ℝ h).integral_comp_comm hi
variable {ι : Type*} [Fintype ι]
end Mean
end
end

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
private theorem FunctionalInequalities.Probability.Posterior.line_hasDerivAt (c h : E) :
    HasDerivAt (fun t : ℝ => c + t • h) h 0 := by
  convert! ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add c using 1
  simp only [one_smul]
/-- The `c`-gradient of `ψ` is the posterior mean: `D_c ψ(c, Q)[h] = ⟪h, a(c, Q)⟫`. -/
theorem solution (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) (h : E) :
    fderiv ℝ (fun y => FunctionalInequalities.Probability.Posterior.logPartition μ y Q) c h = ⟪h, FunctionalInequalities.Probability.Posterior.posteriorMean μ c Q⟫ := by
  have hZ : ContDiff ℝ ∞
      (fun y : E =>
        ∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent y Q x) ∂(μ : Measure E)) := by
    simpa only [mul_one] using
      (FunctionalInequalities.Probability.Posterior.contDiff_weighted_integral_quadraticExponent_of_compact_readable μ hc
        (f := fun _ : E => (1 : ℝ)) measurable_const
        (C := 1) (by norm_num) (by intro x hx; simp) Q)
  have hpos (y : E) :
      0 < ∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent y Q x) ∂(μ : Measure E) :=
    integral_exp_pos
      (FunctionalInequalities.Probability.Posterior.integrable_exp_of_compact μ hc (by
        unfold FunctionalInequalities.Probability.Posterior.quadraticExponent
        fun_prop))
  have hlog : ContDiff ℝ ∞
      (fun y : E =>
        Real.log (∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent y Q x)
          ∂(μ : Measure E))) :=
    hZ.log (fun y => (hpos y).ne')
  have hφ : Continuous (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q) := by
    unfold FunctionalInequalities.Probability.Posterior.quadraticExponent
    fun_prop
  have hg : Continuous (fun x : E => ⟪h, x⟫) := by
    fun_prop
  have hN := FunctionalInequalities.Probability.Posterior.hasDerivAt_weighted_integral_of_compact_readable μ hc
    (φ := FunctionalInequalities.Probability.Posterior.quadraticExponent c Q) (g := fun x : E => ⟪h, x⟫)
    (f := fun _ : E => (1 : ℝ)) hφ hg measurable_const
    (C := 1) (by norm_num) (by intro x hx; simp)
  simp only [mul_one] at hN
  have hphase (t : ℝ) :
      FunctionalInequalities.Probability.Posterior.quadraticExponent (c + t • h) Q =
        fun x : E => FunctionalInequalities.Probability.Posterior.quadraticExponent c Q x + t * ⟪h, x⟫ := by
    funext x
    simp only [FunctionalInequalities.Probability.Posterior.quadraticExponent, inner_add_left, real_inner_smul_left]
    ring
  have hN' :
      HasDerivAt
        (fun t : ℝ =>
          ∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent (c + t • h) Q x)
            ∂(μ : Measure E))
        (∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q x) * ⟪h, x⟫
          ∂(μ : Measure E)) 0 := by
    simpa only [hphase] using hN
  have hlogD :=
    ((hlog.differentiable (by norm_num) c).hasFDerivAt).comp_hasDerivAt_of_eq
      (0 : ℝ) (FunctionalInequalities.Probability.Posterior.line_hasDerivAt c h) (by simp)
  have hlogDfun :
      ((fun y : E =>
          Real.log (∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent y Q x)
            ∂(μ : Measure E))) ∘
        (fun t : ℝ => c + t • h)) =
      (fun t : ℝ =>
        Real.log (∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent (c + t • h) Q x)
          ∂(μ : Measure E))) := by
    funext t
    rfl
  rw [hlogDfun] at hlogD
  have hlogN := hN'.log (by simpa using (hpos c).ne')
  have hlogN' :
      HasDerivAt
        (fun t : ℝ =>
          Real.log (∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent (c + t • h) Q x)
            ∂(μ : Measure E)))
        ((∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q x) ∂(μ : Measure E))⁻¹ *
          (∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q x) * ⟪h, x⟫
            ∂(μ : Measure E))) 0 := by
    simpa only [zero_smul, add_zero, div_eq_mul_inv, mul_comm] using hlogN
  have hderivLog :
      fderiv ℝ
          (fun y : E =>
            Real.log (∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent y Q x)
              ∂(μ : Measure E))) c h =
        (∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q x) ∂(μ : Measure E))⁻¹ *
          (∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q x) * ⟪h, x⟫
            ∂(μ : Measure E)) :=
    hlogD.unique hlogN'
  change fderiv ℝ
      (fun y : E =>
        Real.log (∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent y Q x)
          ∂(μ : Measure E))) c h = _
  calc
    fderiv ℝ
        (fun y : E =>
          Real.log (∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent y Q x)
            ∂(μ : Measure E))) c h =
        (∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q x) ∂(μ : Measure E))⁻¹ *
          (∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q x) * ⟪h, x⟫
            ∂(μ : Measure E)) := hderivLog
    _ = (∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q x) * ⟪h, x⟫
          ∂(μ : Measure E)) /
          ∫ x, Real.exp (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q x) ∂(μ : Measure E) := by
      rw [div_eq_mul_inv]
      ring
    _ = ∫ x, ⟪h, x⟫
        ∂((μ : Measure E).tilted (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q)) := by
      rw [FunctionalInequalities.Probability.Posterior.integral_tilted_eq_div]
    _ = ⟪h, FunctionalInequalities.Probability.Posterior.posteriorMean μ c Q⟫ :=
      FunctionalInequalities.Probability.Posterior.integral_inner_eq_inner_posteriorMean μ hc c Q h

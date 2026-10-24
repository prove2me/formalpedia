-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Mollification.integral_inner_convolution_eq_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:56:15.776381+00:00
-- url     : https://prove2.me/submissions/92b73a75-c15a-416a-94df-d14bad81ec27

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.SpecificCodomains.Pi

noncomputable section
open MeasureTheory Filter Topology Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Mollification
end FunctionalInequalities.Analysis.Mollification
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Mollification
open FunctionalInequalities.Analysis.BakryEmery
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {m : Measure V} [m.IsAddHaarMeasure]
section Adjoint
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (φ : ContDiffBump (0 : V))
namespace FunctionalInequalities.Analysis.Mollification
end FunctionalInequalities.Analysis.Mollification
open FunctionalInequalities.Analysis.Mollification in
/-- **The mollifier is symmetric for the `L²` pairing**: for an integrable `a` and a continuous
compactly supported `b`, `∫ ⟪ρ ⋆ a, b⟫ = ∫ ⟪a, ρ ⋆ b⟫`. The bump is even, so no reflection of the
kernel appears. -/
theorem solution {a b : V → E} (ha : Integrable a m) (hb : Continuous b)
    (hbc : HasCompactSupport b) :
    ∫ x, ⟪(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] a) x, b x⟫ ∂m =
      ∫ y, ⟪a y, (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] b) y⟫ ∂m := by
  obtain ⟨C, hC⟩ := hb.bounded_above_of_compact_support hbc
  have hρi : Integrable (φ.normed m) m := φ.integrable_normed
  have hρm : Measurable (φ.normed m) := φ.continuous_normed.measurable
  -- the two product integrands
  have hI₁ : Integrable (fun p : V × V => φ.normed m p.2 * ⟪a (p.1 - p.2), b p.1⟫) (m.prod m) := by
    have h0 := hρi.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) ha
    refine (h0.norm.mul_const C).mono' ?_ ?_
    · refine ((hρm.comp measurable_snd).aestronglyMeasurable.mul ?_)
      refine (AEStronglyMeasurable.inner ?_ (hb.comp continuous_fst).aestronglyMeasurable)
      exact ha.1.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_of_right_invariant m m)
    · refine Filter.Eventually.of_forall fun p => ?_
      simp only [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (φ.nonneg_normed _), norm_mul]
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg_normed _)
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))
  have hI₂ : Integrable (fun p : V × V => φ.normed m p.1 * ⟪a p.2, b (p.2 + p.1)⟫) (m.prod m) := by
    have h0 := hρi.mul_prod ha.norm
    refine (h0.mul_const C).mono' ?_ ?_
    · refine ((hρm.comp measurable_fst).aestronglyMeasurable.mul ?_)
      refine (AEStronglyMeasurable.inner ?_ ?_)
      · exact ha.1.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_snd)
      · exact (hb.comp (continuous_snd.add continuous_fst)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun p => ?_
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed _)]
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg_normed _)
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))
  -- left side: pull the pairing inside, swap, translate
  have hL : ∀ x, ⟪(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] a) x, b x⟫ =
      ∫ t, φ.normed m t * ⟪a (x - t), b x⟫ ∂m := by
    intro x
    have hint : Integrable (fun t => (ContinuousLinearMap.lsmul ℝ ℝ (φ.normed m t)) (a (x - t))) m :=
      HasCompactSupport.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ.hasCompactSupport_normed (μ := m)) φ.continuous_normed ha.locallyIntegrable x
    rw [convolution_def, real_inner_comm, ← integral_inner hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, real_inner_smul_right, real_inner_comm]
  have hR : ∀ y, ⟪a y, (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] b) y⟫ =
      ∫ t, φ.normed m t * ⟪a y, b (y + t)⟫ ∂m := by
    intro y
    have hint : Integrable (fun t => φ.normed m t • b (y + t)) m := by
      refine hρi.smul_of_top_left (memLp_top_of_bound ?_ C (Filter.Eventually.of_forall fun t => hC _))
      exact (hb.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    rw [convolution_def, ← integral_neg_eq_self (fun t => (ContinuousLinearMap.lsmul ℝ ℝ
      (φ.normed m t)) (b (y - t))) m]
    simp only [ContinuousLinearMap.lsmul_apply, φ.normed_neg, sub_neg_eq_add]
    rw [← integral_inner hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [real_inner_smul_right]
  simp only [hL, hR]
  rw [integral_integral_swap hI₁]
  have hmid : ∀ t, ∫ x, φ.normed m t * ⟪a (x - t), b x⟫ ∂m =
      ∫ y, φ.normed m t * ⟪a y, b (y + t)⟫ ∂m := by
    intro t
    rw [integral_const_mul, integral_const_mul]
    congr 1
    have := integral_sub_right_eq_self (μ := m) (fun y => ⟪a y, b (y + t)⟫) t
    simp only [sub_add_cancel] at this
    exact this
  simp only [hmid]
  exact integral_integral_swap hI₂

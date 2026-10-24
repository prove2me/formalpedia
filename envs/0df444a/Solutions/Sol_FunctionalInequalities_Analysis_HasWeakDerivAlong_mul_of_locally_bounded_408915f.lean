-- Prove2me | solution 1 for FunctionalInequalities.Analysis.HasWeakDerivAlong.mul_of_locally_bounded_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:01:37.40898+00:00
-- url     : https://prove2.me/submissions/8bd488bd-f3b5-4bc3-acb4-b477baeee18e

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_mul_contDiff_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_mul_of_locally_memLp_two_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_memLp_mul_of_hasCompactSupport_408915f

noncomputable section
open MeasureTheory
open scoped ContDiff
universe u
section WeakNegativeExponential
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section StructuredSpace
variable {E : Type*}
variable [NormedAddCommGroup E]
section NormedSpace
variable [NormedSpace ℝ E]
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
end
end
end WeakNegativeExponential
section WeakLocalBoundedProducts
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis.HasWeakDerivAlong
end FunctionalInequalities.Analysis.HasWeakDerivAlong
open FunctionalInequalities.Analysis.HasWeakDerivAlong in
/-- Locally essentially bounded weak factors have their actual directional
product derivative, locally L2. No global bound or C1/C2 regularity is assumed. -/
theorem solution {n : ℕ}
    {f df g dg : EuclideanSpace ℝ (Fin n) → ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    (hf : FunctionalInequalities.Analysis.HasWeakDerivAlong f df v) (hg : FunctionalInequalities.Analysis.HasWeakDerivAlong g dg v)
    (hf_top : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f (⊤ : ENNReal) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hg_top : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp g (⊤ : ENNReal) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hdf2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp df 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hdg2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp dg 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => f x * g x)
      (fun x => df x * g x + f x * dg x) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => df x * g x + f x * dg x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  have hf2 :
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    intro S hS
    let : IsFiniteMeasure
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (hf_top S hS).mono_exponent le_top
  have hg2 :
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp g 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    intro S hS
    let : IsFiniteMeasure
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (hg_top S hS).mono_exponent le_top
  have hlocal :
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => df x * g x + f x * dg x) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    intro S hS
    have hfirst : MemLp (fun x => df x * g x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
      simpa only [mul_comm] using (hdf2 S hS).mul' (hg_top S hS)
    exact hfirst.add ((hdg2 S hS).mul' (hf_top S hS))
  have hproduct : LocallyIntegrable (fun x => f x * g x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply locallyIntegrable_iff.mpr
    intro S hS
    let : IsFiniteMeasure
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    have hp : MemLp (fun x => f x * g x) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      (hg_top S hS).mul' (hf_top S hS)
    exact hp.integrable le_top
  have hdensity : LocallyIntegrable (fun x => df x * g x + f x * dg x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply locallyIntegrable_iff.mpr
    intro S hS
    let : IsFiniteMeasure
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (hlocal S hS).integrable (by norm_num)
  refine ⟨⟨hproduct, hdensity, ?_⟩, hlocal⟩
  intro ψ hψ hψc
  obtain ⟨χ, hχ, hχc, hχnear⟩ := weak_exists_compact_contDiff_eq_one_near hψc
  have hχon (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ tsupport ψ) :
      χ x = 1 ∧ fderiv ℝ χ x v = 0 := by
    have he := hχnear x hx
    refine ⟨he.eq_of_nhds, ?_⟩
    rw [he.fderiv_eq]
    simp
  have hcut_top
      (a : EuclideanSpace ℝ (Fin n) → ℝ)
      (ha : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp a (⊤ : ENNReal)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
      MemLp (fun x => χ x * a x) (⊤ : ENNReal)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    classical
    have hKm : MeasurableSet (tsupport χ) :=
      (isClosed_tsupport χ).measurableSet
    have hind : MemLp ((tsupport χ).indicator a) (⊤ : ENNReal)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      (memLp_indicator_iff_restrict hKm).mpr (ha (tsupport χ) hχc)
    have hχlp : MemLp χ (⊤ : ENNReal)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      hχ.continuous.memLp_of_hasCompactSupport hχc
    have hm : MemLp (fun x => χ x * ((tsupport χ).indicator a) x)
        (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      hind.mul' hχlp
    convert hm using 1
    funext x
    by_cases hx : x ∈ tsupport χ
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx,
        zero_mul, zero_mul]
  have hχd : Continuous (fun x => fderiv ℝ χ x v) :=
    (hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hχdc : HasCompactSupport (fun x => fderiv ℝ χ x v) :=
    hχc.fderiv_apply ℝ v
  have hχdf2 : MemLp
      (fun x => χ x * df x + fderiv ℝ χ x v * f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (FunctionalInequalities.Analysis.memLp_mul_of_hasCompactSupport_408915f hχ.continuous hχc hdf2).add
      (FunctionalInequalities.Analysis.memLp_mul_of_hasCompactSupport_408915f hχd hχdc hf2)
  have hχdg2 : MemLp
      (fun x => χ x * dg x + fderiv ℝ χ x v * g x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (FunctionalInequalities.Analysis.memLp_mul_of_hasCompactSupport_408915f hχ.continuous hχc hdg2).add
      (FunctionalInequalities.Analysis.memLp_mul_of_hasCompactSupport_408915f hχd hχdc hg2)
  have hw := (hf.mul_contDiff_408915f hχ hχc).mul_of_locally_memLp_two_408915f
    (hg.mul_contDiff_408915f hχ hχc) (hcut_top f hf_top) (hcut_top g hg_top)
    (fun S _ => hχdf2.restrict S) (fun S _ => hχdg2.restrict S)
  have hleft :
      (∫ x, (f x * g x) * fderiv ℝ ψ x v) =
        ∫ x, ((χ x * f x) * (χ x * g x)) * fderiv ℝ ψ x v := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change (f x * g x) * fderiv ℝ ψ x v =
        ((χ x * f x) * (χ x * g x)) * fderiv ℝ ψ x v
      by_cases hx : x ∈ tsupport ψ
      · rw [(hχon x hx).1]
        simp only [one_mul]
      · rw [weak_fderiv_apply_eq_zero_off_tsupport hx v]
        simp only [mul_zero]
  have hright :
      (∫ x, ((χ x * df x + fderiv ℝ χ x v * f x) * (χ x * g x) +
        (χ x * f x) * (χ x * dg x + fderiv ℝ χ x v * g x)) * ψ x) =
        ∫ x, (df x * g x + f x * dg x) * ψ x := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change ((χ x * df x + fderiv ℝ χ x v * f x) * (χ x * g x) +
        (χ x * f x) * (χ x * dg x + fderiv ℝ χ x v * g x)) * ψ x =
        (df x * g x + f x * dg x) * ψ x
      by_cases hx : x ∈ tsupport ψ
      · obtain ⟨hone, hzero⟩ := hχon x hx
        rw [hone, hzero]
        simp only [one_mul, zero_mul, add_zero]
      · rw [image_eq_zero_of_notMem_tsupport hx]
        simp only [mul_zero]
  calc
    (∫ x, (f x * g x) * fderiv ℝ ψ x v) =
        ∫ x, ((χ x * f x) * (χ x * g x)) * fderiv ℝ ψ x v := hleft
    _ = -(∫ x, ((χ x * df x + fderiv ℝ χ x v * f x) * (χ x * g x) +
        (χ x * f x) * (χ x * dg x + fderiv ℝ χ x v * g x)) * ψ x) :=
      hw.1.2.2 ψ hψ hψc
    _ = -(∫ x, (df x * g x + f x * dg x) * ψ x) :=
      congrArg Neg.neg hright

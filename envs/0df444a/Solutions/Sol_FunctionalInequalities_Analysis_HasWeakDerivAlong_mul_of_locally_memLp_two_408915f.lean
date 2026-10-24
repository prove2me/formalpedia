-- Prove2me | solution 1 for FunctionalInequalities.Analysis.HasWeakDerivAlong.mul_of_locally_memLp_two_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:59:54.709542+00:00
-- url     : https://prove2.me/submissions/68d72cfc-a2ae-4865-ad8d-307250acb7a3

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
import Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_mul_of_memLp_two_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_memLp_mul_of_hasCompactSupport_408915f

noncomputable section
open MeasureTheory
open scoped ContDiff
section WeakProducts
open MeasureTheory Filter Set Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace Topology
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
/-- Bounded weak factors with compact-local L2 derivatives have the actual
weak product derivative, which is itself L2 on every compact set. -/
theorem solution {n : ℕ}
    {f df g dg : EuclideanSpace ℝ (Fin n) → ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    (hf : FunctionalInequalities.Analysis.HasWeakDerivAlong f df v) (hg : FunctionalInequalities.Analysis.HasWeakDerivAlong g dg v)
    (hf_top : MemLp f (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hg_top : MemLp g (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hdf2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp df 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hdg2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp dg 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => f x * g x)
      (fun x => df x * g x + f x * dg x) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => df x * g x + f x * dg x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  have hlocal :
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => df x * g x + f x * dg x) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    intro S hS
    have hfirst : MemLp (fun x => df x * g x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
      simpa only [mul_comm] using (hdf2 S hS).mul' (hg_top.restrict S)
    exact hfirst.add ((hdg2 S hS).mul' (hf_top.restrict S))
  have hproduct : MemLp (fun x => f x * g x) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hg_top.mul' hf_top
  have hdensity : LocallyIntegrable (fun x => df x * g x + f x * dg x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply locallyIntegrable_iff.mpr
    intro S hS
    let : IsFiniteMeasure
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (hlocal S hS).integrable (by norm_num)
  refine ⟨⟨hproduct.locallyIntegrable le_top, hdensity, ?_⟩, hlocal⟩
  intro ψ hψ hψc
  obtain ⟨R, hR⟩ := hψc.isBounded.subset_ball (0 : EuclideanSpace ℝ (Fin n))
  let χ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    { rIn := max R 0 + 1
      rOut := max R 0 + 2
      rIn_pos := by
        have hnonneg := le_max_right R 0
        linarith
      rIn_lt_rOut := by linarith }
  have hχ : ContDiff ℝ 1 (χ : EuclideanSpace ℝ (Fin n) → ℝ) :=
    χ.contDiff
  have hχc : HasCompactSupport (χ : EuclideanSpace ℝ (Fin n) → ℝ) :=
    χ.hasCompactSupport
  have hχon (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ tsupport ψ) :
      χ x = 1 ∧ fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v = 0 := by
    have hradius : R ≤ χ.rIn := by
      change R ≤ max R 0 + 1
      have hle := le_max_left R 0
      linarith
    have he := χ.eventuallyEq_one_of_mem_ball
      ((ball_subset_ball hradius) (hR hx))
    refine ⟨he.eq_of_nhds, ?_⟩
    simp [he.fderiv_eq]
  have hχ2 : MemLp (χ : EuclideanSpace ℝ (Fin n) → ℝ) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hχ.continuous.memLp_of_hasCompactSupport hχc
  have hχd : Continuous
      (fun x => fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v) :=
    (hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hχdc : HasCompactSupport
      (fun x => fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v) :=
    hχc.fderiv_apply ℝ v
  have hχd2 : MemLp
      (fun x => fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hχd.memLp_of_hasCompactSupport hχdc
  have hχf2 : MemLp (fun x => χ x * f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hf_top.mul' hχ2
  have hχg2 : MemLp (fun x => χ x * g x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hg_top.mul' hχ2
  have hχdf2 : MemLp
      (fun x => χ x * df x +
        fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (FunctionalInequalities.Analysis.memLp_mul_of_hasCompactSupport_408915f hχ.continuous hχc hdf2).add (hf_top.mul' hχd2)
  have hχdg2 : MemLp
      (fun x => χ x * dg x +
        fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * g x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (FunctionalInequalities.Analysis.memLp_mul_of_hasCompactSupport_408915f hχ.continuous hχc hdg2).add (hg_top.mul' hχd2)
  have hw := (hf.mul_contDiff_408915f hχ hχc).mul_of_memLp_two_408915f
    (hg.mul_contDiff_408915f hχ hχc) hχf2 hχdf2 hχg2 hχdg2
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
      · rw [fderiv_of_notMem_tsupport ℝ hx]
        simp only [zero_apply, mul_zero]
  have hright :
      (∫ x, ((χ x * df x +
          fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * f x) *
          (χ x * g x) +
        (χ x * f x) * (χ x * dg x +
          fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * g x)) * ψ x) =
        ∫ x, (df x * g x + f x * dg x) * ψ x := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change ((χ x * df x +
          fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * f x) *
          (χ x * g x) +
        (χ x * f x) * (χ x * dg x +
          fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * g x)) * ψ x =
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
    _ = -(∫ x, ((χ x * df x +
          fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * f x) *
          (χ x * g x) +
        (χ x * f x) * (χ x * dg x +
          fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x v * g x)) * ψ x) :=
      hw.2.2 ψ hψ hψc
    _ = -(∫ x, (df x * g x + f x * dg x) * ψ x) :=
      congrArg Neg.neg hright

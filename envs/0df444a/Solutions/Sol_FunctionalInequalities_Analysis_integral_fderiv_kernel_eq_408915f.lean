-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integral_fderiv_kernel_eq_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:41:19.099215+00:00
-- url     : https://prove2.me/submissions/8761729f-8b50-4969-b686-a2e7dd10bb7a

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
section LipschitzConvolution
open MeasureTheory
open scoped Convolution
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
variable [BorelSpace E]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
 theorem solution
    {F : E → E} {G : NNReal} (hF : LipschitzWith G F)
    (k : E → ℝ) (hk : ContDiff ℝ 1 k) (hc : HasCompactSupport k)
    (x v : E) (ℓ : E →L[ℝ] ℝ) :
    (∫ t, fderiv ℝ k t v * ℓ (F (x - t))) =
      ∫ t, k t * ℓ (fderiv ℝ F (x - t) v) := by
  let g : E → ℝ := fun y => k (x - y)
  have hgc : HasCompactSupport g :=
    hc.comp_homeomorph (Homeomorph.subLeft x)
  have hgd : ContDiff ℝ 1 g :=
    hk.comp (contDiff_const.sub contDiff_id)
  obtain ⟨D, hg⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hgc hgd (by decide)
  have hdg (y : E) :
      lineDeriv ℝ g y (-v) = fderiv ℝ k (x - y) v := by
    change lineDeriv ℝ (k ∘ (fun z : E => x - z)) y (-v) = _
    simpa only [ContinuousLinearMap.comp_apply, neg_apply,
      ContinuousLinearMap.id_apply, neg_neg] using
      ((((hk.differentiable (by decide)) (x - y)).hasFDerivAt.comp y
        ((hasFDerivAt_id (𝕜 := ℝ) y).const_sub x)).hasLineDerivAt (-v)).lineDeriv
  have hdF :
      ∀ᵐ y ∂(volume : Measure E),
        lineDeriv ℝ (ℓ ∘ F) y v = ℓ (fderiv ℝ F y v) := by
    filter_upwards [hF.ae_differentiableAt (μ := (volume : Measure E))] with y hy
    exact ((ℓ.hasFDerivAt.comp y hy.hasFDerivAt).hasLineDerivAt v).lineDeriv
  have hb :=
    (ℓ.lipschitz.comp hF).integral_lineDeriv_mul_eq
      (μ := (volume : Measure E)) hg hgc v
  have he :
      (∫ y, lineDeriv ℝ (ℓ ∘ F) y v * g y) =
        ∫ y, k (x - y) * ℓ (fderiv ℝ F y v) := by
    apply integral_congr_ae
    filter_upwards [hdF] with y hy
    rw [hy]
    exact mul_comm _ _
  rw [he] at hb
  have hb' :
      (∫ y, fderiv ℝ k (x - y) v * ℓ (F y)) =
        ∫ y, k (x - y) * ℓ (fderiv ℝ F y v) := by
    simpa only [hdg, Function.comp_apply] using hb.symm
  have ha :
      (∫ y, fderiv ℝ k (x - y) v * ℓ (F y)) =
        ∫ t, fderiv ℝ k t v * ℓ (F (x - t)) := by
    simpa only [sub_sub_cancel] using
      integral_sub_left_eq_self
        (fun t => fderiv ℝ k t v * ℓ (F (x - t)))
        (volume : Measure E) x
  have hz :
      (∫ y, k (x - y) * ℓ (fderiv ℝ F y v)) =
        ∫ t, k t * ℓ (fderiv ℝ F (x - t) v) := by
    simpa only [sub_sub_cancel] using
      integral_sub_left_eq_self
        (fun t => k t * ℓ (fderiv ℝ F (x - t) v))
        (volume : Measure E) x
  exact ha.symm.trans (hb'.trans hz)

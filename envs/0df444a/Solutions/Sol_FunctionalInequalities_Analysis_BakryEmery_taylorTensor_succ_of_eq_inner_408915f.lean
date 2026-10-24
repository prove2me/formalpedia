-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.taylorTensor_succ_of_eq_inner_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:52:45.362763+00:00
-- url     : https://prove2.me/submissions/b2d4ba49-8a17-4921-b157-195b1157eeca

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_iteratedFDeriv_comp_perm_of_contDiff_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_iteratedFDeriv_inner_self_apply_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_perm_inner_init_last_408915f

noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff ENNReal
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section Lp
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Lemma 3.6 from the tilt identity: if `F_g(w) = ⟪w, F_G(w)⟫` for every `w` with `F_G` smooth,
then `T_{d+1} g = S_{d+1} T_d G`. This is the tensor part of the proof of
`taylorTensor_neg_weightedLaplacian`, isolated from the smooth compactly supported setting. -/
theorem solution (μ : Measure E) {g : E → ℝ} {G : E → E}
    (hG : ContDiff ℝ ∞ (FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ G))
    (hEq : FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ g = fun w => ⟪w, FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ G w⟫) (d : ℕ) :
    FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ g (d + 1) = FunctionalInequalities.Analysis.Tensor.symmetrizeML (FunctionalInequalities.Analysis.Tensor.appendInner (FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ G d)) := by
  set Φ := FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ G with hΦ
  ext h
  simp only [FunctionalInequalities.Analysis.BakryEmery.taylorTensor, FunctionalInequalities.Analysis.Tensor.symmetrizeML, FunctionalInequalities.Analysis.Tensor.appendInner,
    smul_apply,
    sum_apply,
    ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurryRight_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe]
  rw [hEq, ← hΦ]
  rw [FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_inner_self_apply_408915f hG d 0 h]
  simp only [inner_zero_left, zero_add, Function.comp_apply]
  change
    ((d + 1).factorial : ℝ)⁻¹ •
        ∑ k : Fin (d + 1), ⟪h k, (iteratedFDeriv ℝ d Φ 0) (k.removeNth h)⟫ =
      ((d + 1).factorial : ℝ)⁻¹ •
        ∑ σ : Equiv.Perm (Fin (d + 1)),
          ⟪((d.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ d Φ 0) (Fin.init (h ∘ σ)),
            h (σ (Fin.last d))⟫
  have hs : (∑ σ : Equiv.Perm (Fin (d + 1)),
        ⟪(iteratedFDeriv ℝ d Φ 0) (Fin.init (h ∘ σ)), h (σ (Fin.last d))⟫) =
      (d.factorial : ℝ) *
        ∑ k : Fin (d + 1), ⟪(iteratedFDeriv ℝ d Φ 0) (k.removeNth h), h k⟫ := by
    apply FunctionalInequalities.Analysis.Tensor.sum_perm_inner_init_last_408915f
    intro τ v
    exact FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_comp_perm_of_contDiff_408915f hG d 0 v τ
  have hsum : (∑ σ : Equiv.Perm (Fin (d + 1)),
        ⟪((d.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ d Φ 0) (Fin.init (h ∘ σ)),
          h (σ (Fin.last d))⟫) =
      ∑ k : Fin (d + 1), ⟪(iteratedFDeriv ℝ d Φ 0) (k.removeNth h), h k⟫ := by
    simp_rw [smul_apply, real_inner_smul_left]
    rw [← Finset.mul_sum, hs]
    field_simp [Nat.factorial_ne_zero]
  rw [hsum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => real_inner_comm _ _

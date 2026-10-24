-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.norm_iteratedFDeriv_cutoff_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:46:15.202502+00:00
-- url     : https://prove2.me/submissions/c08dc489-ee7a-4322-8114-4e91dc005103

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Distribution.TemperateGrowth
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

noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
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
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- Uniform derivative bounds: for each order `n`, `‖∇ⁿχ_R‖ ≤ C` for every `R ≥ 1`. -/
theorem solution (n : ℕ) :
    ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ x : E, ‖iteratedFDeriv ℝ n (FunctionalInequalities.Analysis.BakryEmery.cutoff R) x‖ ≤ C := by
    have hcont :
        Continuous (fun x : E =>
          iteratedFDeriv ℝ n
            ((FunctionalInequalities.Analysis.BakryEmery.unitBump : ContDiffBump (0 : E)) : E → ℝ) x) := by
      exact
        (FunctionalInequalities.Analysis.BakryEmery.unitBump : ContDiffBump (0 : E)).contDiff
          |>.continuous_iteratedFDeriv (n := n) (by simp)
    have hcomp :
        HasCompactSupport (fun x : E =>
          iteratedFDeriv ℝ n
            ((FunctionalInequalities.Analysis.BakryEmery.unitBump : ContDiffBump (0 : E)) : E → ℝ) x) :=
      (FunctionalInequalities.Analysis.BakryEmery.unitBump : ContDiffBump (0 : E)).hasCompactSupport.iteratedFDeriv n
    obtain ⟨C₀, hC₀⟩ :=
      hcont.bounded_above_of_compact_support hcomp
    let C : ℝ := max C₀ 0
    have hC : ∀ x : E,
        ‖iteratedFDeriv ℝ n
            ((FunctionalInequalities.Analysis.BakryEmery.unitBump : ContDiffBump (0 : E)) : E → ℝ) x‖ ≤ C := by
      intro x
      exact (hC₀ x).trans (le_max_left _ _)
    have hC_nonneg : 0 ≤ C := le_max_right _ _
    refine ⟨C, ?_⟩
    intro R hR x
    have hR0 : 0 ≤ R := le_trans zero_le_one hR
    have hinv : ‖R⁻¹‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hR0)]
      exact inv_le_one_of_one_le₀ hR
    have hpow : ‖R⁻¹‖ ^ n ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) hinv
    have hderiv :
        iteratedFDeriv ℝ n (FunctionalInequalities.Analysis.BakryEmery.cutoff R) x =
          (R⁻¹) ^ n •
            iteratedFDeriv ℝ n
              ((FunctionalInequalities.Analysis.BakryEmery.unitBump : ContDiffBump (0 : E)) : E → ℝ) (R⁻¹ • x) := by
      change
        iteratedFDeriv ℝ n
            (fun z : E =>
              ((FunctionalInequalities.Analysis.BakryEmery.unitBump : ContDiffBump (0 : E)) : E → ℝ) (R⁻¹ • z)) x =
          (R⁻¹) ^ n •
            iteratedFDeriv ℝ n
              ((FunctionalInequalities.Analysis.BakryEmery.unitBump : ContDiffBump (0 : E)) : E → ℝ) (R⁻¹ • x)
      simpa [inv_pow] using
        congrFun
          (iteratedFDeriv_comp_const_smul (𝕜 := ℝ)
            (f := ((FunctionalInequalities.Analysis.BakryEmery.unitBump : ContDiffBump (0 : E)) : E → ℝ))
            R⁻¹ (FunctionalInequalities.Analysis.BakryEmery.unitBump : ContDiffBump (0 : E)).contDiff) x
    calc
      ‖iteratedFDeriv ℝ n (FunctionalInequalities.Analysis.BakryEmery.cutoff R) x‖ =
          ‖R⁻¹‖ ^ n *
            ‖iteratedFDeriv ℝ n
              ((FunctionalInequalities.Analysis.BakryEmery.unitBump : ContDiffBump (0 : E)) : E → ℝ) (R⁻¹ • x)‖ := by
        rw [hderiv, norm_smul, norm_pow]
      _ ≤ ‖R⁻¹‖ ^ n * C :=
        mul_le_mul_of_nonneg_left (hC _) (pow_nonneg (norm_nonneg _) n)
      _ ≤ 1 * C :=
        mul_le_mul_of_nonneg_right hpow hC_nonneg
      _ = C := by simp

-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.abs_laplacian_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:41:14.370366+00:00
-- url     : https://prove2.me/submissions/2e3dc9a0-e316-4086-9442-4be04e5042f0

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
/-- `|Δg(x)| ≤ dim E · ‖∇²g(x)‖`. -/
theorem solution (g : E → ℝ) (x : E) :
    |Laplacian.laplacian g x| ≤ Module.finrank ℝ E * ‖iteratedFDeriv ℝ 2 g x‖ := by
    rw [FunctionalInequalities.Analysis.BakryEmery.laplacian_eq_sum_fderiv_fderiv]
    have hnorm (i : Fin (Module.finrank ℝ E)) :
        ‖(stdOrthonormalBasis ℝ E) i‖ = 1 :=
      (stdOrthonormalBasis ℝ E).norm_eq_one i
    have hterm (i : Fin (Module.finrank ℝ E)) :
        |(fderiv ℝ (fderiv ℝ g) x ((stdOrthonormalBasis ℝ E) i))
            ((stdOrthonormalBasis ℝ E) i)| ≤
          ‖iteratedFDeriv ℝ 2 g x‖ := by
      have h :=
        (iteratedFDeriv ℝ 2 g x).le_opNorm
          ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i]
      rw [iteratedFDeriv_two_apply] at h
      simpa [Real.norm_eq_abs] using h
    calc
      |∑ i : Fin (Module.finrank ℝ E),
          (fderiv ℝ (fderiv ℝ g) x ((stdOrthonormalBasis ℝ E) i))
            ((stdOrthonormalBasis ℝ E) i)| ≤
          ∑ i : Fin (Module.finrank ℝ E),
            |(fderiv ℝ (fderiv ℝ g) x ((stdOrthonormalBasis ℝ E) i))
              ((stdOrthonormalBasis ℝ E) i)| := by
        apply Finset.abs_sum_le_sum_abs
      _ ≤ ∑ i : Fin (Module.finrank ℝ E), ‖iteratedFDeriv ℝ 2 g x‖ := by
        exact Finset.sum_le_sum (fun i _ => hterm i)
      _ = (Module.finrank ℝ E : ℝ) * ‖iteratedFDeriv ℝ 2 g x‖ := by
        simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]

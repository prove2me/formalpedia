-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.integrable_of_norm_le_pow_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:45:35.341317+00:00
-- url     : https://prove2.me/submissions/0e9b694c-65a5-4bb1-a5ff-e82f85ca2dd7

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
omit [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Under all exponential moments, polynomially bounded measurable functions are integrable. -/
theorem solution {F : Type*} [NormedAddCommGroup F] (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {g : E → F}
    (hg : AEStronglyMeasurable g μ) {C : ℝ} {k : ℕ} (hgb : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖) ^ k) :
    Integrable g μ := by
    have hpow : ∀ t : ℝ, 0 ≤ t → ∀ n : ℕ,
        (1 + t) ^ n ≤ Real.exp ((n : ℝ) * t) := by
      intro t ht n
      induction n with
      | zero =>
          simp
      | succ n ih =>
          calc
            (1 + t) ^ n.succ = (1 + t) ^ n * (1 + t) := by
              rw [pow_succ]
            _ ≤ Real.exp ((n : ℝ) * t) * Real.exp t := by
              exact
                mul_le_mul ih (by simpa [add_comm] using Real.add_one_le_exp t)
                  (by linarith) (by positivity)
            _ = Real.exp ((n.succ : ℕ) * t) := by
              rw [← Real.exp_add]
              congr 1
              push_cast
              ring
    have hdom : ∀ x : E, ‖g x‖ ≤ max C 0 * Real.exp ((k : ℝ) * ‖x‖) := by
      intro x
      have hp : (1 + ‖x‖) ^ k ≤ Real.exp ((k : ℝ) * ‖x‖) :=
        hpow ‖x‖ (norm_nonneg x) k
      calc
        ‖g x‖ ≤ C * (1 + ‖x‖) ^ k := hgb x
        _ ≤ max C 0 * (1 + ‖x‖) ^ k := by
          exact
            mul_le_mul_of_nonneg_right (le_max_left C 0)
              (pow_nonneg (by positivity) k)
        _ ≤ max C 0 * Real.exp ((k : ℝ) * ‖x‖) := by
          exact mul_le_mul_of_nonneg_left hp (le_max_right C 0)
    refine ((hexp (k : ℝ)).const_mul (max C 0)).mono' hg
      (ae_of_all _ (fun x => ?_))
    simpa [smul_eq_mul] using hdom x

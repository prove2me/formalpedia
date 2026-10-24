-- Prove2me | solution 1 for FunctionalInequalities.Probability.tendsto_variance_quadratic_matrix_forms_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:39:59.496699+00:00
-- url     : https://prove2.me/submissions/57e9ac44-5b55-4fda-ae4c-66b06d46a986

import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Theorems.Thm_FunctionalInequalities_Probability_tendsto_variance_finite_linear_combination_408915f

noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities.Probability in
set_option maxHeartbeats 500000 in
theorem solution {n : ℕ}
    (mu : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (h4 : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 4 (mu : Measure _))
    {seq : ℕ → Matrix (Fin n) (Fin n) ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hseq : Tendsto seq atTop (𝓝 A)) :
    Tendsto (fun k => ProbabilityTheory.variance
      (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, ∑ j, seq k i j * x i * x j) (mu : Measure _))
      atTop (𝓝 (ProbabilityTheory.variance
        (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, ∑ j, A i j * x i * x j) (mu : Measure _))) := by
  classical
  have ht : ENNReal.HolderTriple (4 : ENNReal) 4 2 := by
    constructor
    rw [← ENNReal.coe_ofNat 4, ← ENNReal.coe_ofNat 2,
      ← ENNReal.coe_inv (by norm_num : (4 : NNReal) ≠ 0),
      ← ENNReal.coe_inv (by norm_num : (2 : NNReal) ≠ 0),
      ← ENNReal.coe_add]
    norm_num
  have hcoord (i : Fin n) : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 4 (mu : Measure _) := by
    simpa only [id_eq, EuclideanSpace.inner_basisFun_real] using
      h4.inner_const (𝕜 := ℝ) (EuclideanSpace.basisFun (Fin n) ℝ i)
  have hprod (p : Fin n × Fin n) : MemLp
      (fun x : EuclideanSpace ℝ (Fin n) => x p.1 * x p.2) 2 (mu : Measure _) :=
    (hcoord p.2).mul (hcoord p.1) (hpqr := ht)
  have hc (p : Fin n × Fin n) : Tendsto (fun k => seq k p.1 p.2) atTop (𝓝 (A p.1 p.2)) := by
    have hcont : Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => M p.1 p.2) := by fun_prop
    exact hcont.continuousAt.tendsto.comp hseq
  have h := FunctionalInequalities.Probability.tendsto_variance_finite_linear_combination_408915f mu
    (fun p : Fin n × Fin n => fun x : EuclideanSpace ℝ (Fin n) => x p.1 * x p.2) hprod
    (fun k p => seq k p.1 p.2) (fun p => A p.1 p.2) hc
  simpa only [Fintype.sum_prod_type, mul_assoc] using h

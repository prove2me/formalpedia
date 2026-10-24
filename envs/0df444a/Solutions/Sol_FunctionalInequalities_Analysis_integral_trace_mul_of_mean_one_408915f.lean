-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integral_trace_mul_of_mean_one_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:44:29.752689+00:00
-- url     : https://prove2.me/submissions/7d1f34f9-70d9-424e-9570-ca2ba30366bf

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NoncommRing

noncomputable section
open Matrix MeasureTheory
noncomputable section
open MeasureTheory Matrix
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
set_option maxHeartbeats 400000 in
theorem solution {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] (ρ : Measure Ω) (H : Ω → Matrix ι ι ℝ)
    (hInt : ∀ i j, Integrable (fun y => H y i j) ρ)
    (hmean : ∀ i j, (∫ y, H y i j ∂ρ) = (1 : Matrix ι ι ℝ) i j)
    (B : Matrix ι ι ℝ) :
    Integrable (fun y => Matrix.trace (B * H y)) ρ ∧
      (∫ y, Matrix.trace (B * H y) ∂ρ) = Matrix.trace B := by
  have hterms (i j : ι) : Integrable (fun y => B i j * H y j i) ρ := (hInt j i).const_mul _
  have hsum (i : ι) : Integrable (fun y => ∑ j, B i j * H y j i) ρ := by
    apply integrable_finsetSum
    intro j _
    exact hterms i j
  have ht : Integrable (fun y => Matrix.trace (B * H y)) ρ := by
    change Integrable (fun y => ∑ i, ∑ j, B i j * H y j i) ρ
    apply integrable_finsetSum
    intro i _
    exact hsum i
  refine ⟨ht,?_⟩
  change (∫ y, ∑ i, ∑ j, B i j * H y j i ∂ρ) = _
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hsum i)]
  have he (i : ι) : (∫ y, ∑ j, B i j * H y j i ∂ρ) = B i i := by
    rw [MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hterms i j)]
    calc
      (∑ j, ∫ y, B i j * H y j i ∂ρ) = ∑ j, B i j * (1 : Matrix ι ι ℝ) j i := by
        apply Finset.sum_congr rfl
        intro j _
        rw [integral_const_mul,hmean]
      _ = (B * (1 : Matrix ι ι ℝ)) i i := rfl
      _ = B i i := by rw [Matrix.mul_one]
  simp_rw [he]
  rfl

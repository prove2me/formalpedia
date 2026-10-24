-- Prove2me | solution 1 for FunctionalInequalities.Analysis.legendre_le_of_real_lower_bound_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:24:28.204382+00:00
-- url     : https://prove2.me/submissions/d7641f2c-c237-4b61-9e4e-ed130a4e0c9a

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_BoundedConjugate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
open MeasureTheory Set Metric
open scoped ENNReal Topology RealInnerProductSpace
open FunctionalInequalities
open FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A real floor and bounded effective domain give a finite upper bound for the
actual extended-real Legendre transform, at every primal point. -/
theorem solution
    (φ : E → EReal) (L : NNReal) (m : ℝ)
    (hbot : ∀ y, φ y ≠ ⊥)
    (hdom : ∀ y, φ y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ))
    (hfloor : ∀ y, (m : EReal) ≤ φ y) (x : E) :
    FunctionalInequalities.Analysis.legendre φ x ≤ (((L : ℝ) * ‖x‖ - m : ℝ) : EReal) := by
  classical
  unfold FunctionalInequalities.Analysis.legendre
  refine iSup_le ?_
  intro y
  by_cases hy : φ y = ⊤
  · simp [hy, sub_eq_add_neg]
  · have hyReal : ((φ y).toReal : EReal) = φ y :=
      EReal.coe_toReal hy (hbot y)
    have hm : m ≤ (φ y).toReal := by
      have hm' : (m : EReal) ≤ ((φ y).toReal : EReal) := by
        rw [hyReal]
        exact hfloor y
      exact_mod_cast hm'
    have hynorm : ‖y‖ ≤ (L : ℝ) := by
      simpa [mem_closedBall] using hdom y hy
    have hinner : inner ℝ y x ≤ (L : ℝ) * ‖x‖ :=
      (real_inner_le_norm y x).trans
        (mul_le_mul_of_nonneg_right hynorm (norm_nonneg x))
    calc
      (inner ℝ y x : EReal) - φ y =
          ((inner ℝ y x - (φ y).toReal : ℝ) : EReal) := by
            rw [EReal.coe_sub, hyReal]
      _ ≤ (((L : ℝ) * ‖x‖ - m : ℝ) : EReal) := by
        exact_mod_cast (sub_le_sub hinner hm)

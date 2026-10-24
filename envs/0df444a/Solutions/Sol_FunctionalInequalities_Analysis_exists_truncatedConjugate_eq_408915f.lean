-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_truncatedConjugate_eq_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:06:56.358753+00:00
-- url     : https://prove2.me/submissions/bfad90ed-49b3-4110-849b-1fda76cb7603

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Caffarelli
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Normalization
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
section LT11F2TruncatedConjugate
open Set Metric
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- The supremum is attained and dominates every value on the ball. -/
theorem solution {u : E → ℝ} (hu : Continuous u) {M : ℝ} (hM : 0 ≤ M) (p : E) :
    (∃ x ∈ closedBall (0 : E) M, FunctionalInequalities.Analysis.truncatedConjugate u M p = ⟪p, x⟫ - u x) ∧
      ∀ x ∈ closedBall (0 : E) M, ⟪p, x⟫ - u x ≤ FunctionalInequalities.Analysis.truncatedConjugate u M p := by
  have hc :
      IsCompact ((fun x => ⟪p, x⟫ - u x) '' closedBall (0 : E) M) :=
    (isCompact_closedBall (0 : E) M).image
      ((continuous_const.inner continuous_id).sub hu)
  have hn :
      ((fun x => ⟪p, x⟫ - u x) '' closedBall (0 : E) M).Nonempty :=
    ⟨⟪p, 0⟫ - u 0, ⟨0, mem_closedBall_self hM, rfl⟩⟩
  constructor
  · obtain ⟨x, hx, heq⟩ := hc.sSup_mem hn
    exact ⟨x, hx, heq.symm⟩
  · intro x hx
    exact le_csSup hc.bddAbove ⟨x, hx, rfl⟩

-- Prove2me | solution 1 for FunctionalInequalities.Analysis.convexOn_truncatedConjugate_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:08:29.42003+00:00
-- url     : https://prove2.me/submissions/d6b808ef-97da-41ec-af19-5713e33d340f

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
import Theorems.Thm_FunctionalInequalities_Analysis_exists_truncatedConjugate_eq_408915f

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
/-- The truncated conjugate is convex. -/
theorem solution {u : E → ℝ} (hu : Continuous u) {M : ℝ} (hM : 0 ≤ M) :
    ConvexOn ℝ univ (FunctionalInequalities.Analysis.truncatedConjugate u M) := by
  refine ⟨convex_univ, ?_⟩
  intro p hp q hq a b ha hb hab
  obtain ⟨x, hx, heq⟩ :=
    (FunctionalInequalities.Analysis.exists_truncatedConjugate_eq_408915f hu hM (a • p + b • q)).1
  have hpx := (FunctionalInequalities.Analysis.exists_truncatedConjugate_eq_408915f hu hM p).2 x hx
  have hqx := (FunctionalInequalities.Analysis.exists_truncatedConjugate_eq_408915f hu hM q).2 x hx
  change FunctionalInequalities.Analysis.truncatedConjugate u M (a • p + b • q) ≤
    a * FunctionalInequalities.Analysis.truncatedConjugate u M p + b * FunctionalInequalities.Analysis.truncatedConjugate u M q
  rw [heq]
  calc
    ⟪a • p + b • q, x⟫ - u x =
        a * (⟪p, x⟫ - u x) + b * (⟪q, x⟫ - u x) := by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      nlinarith [congrArg (fun t : ℝ => t * u x) hab]
    _ ≤ a * FunctionalInequalities.Analysis.truncatedConjugate u M p + b * FunctionalInequalities.Analysis.truncatedConjugate u M q :=
      add_le_add (mul_le_mul_of_nonneg_left hpx ha)
        (mul_le_mul_of_nonneg_left hqx hb)

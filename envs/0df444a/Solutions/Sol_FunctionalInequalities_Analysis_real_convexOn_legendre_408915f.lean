-- Prove2me | solution 1 for FunctionalInequalities.Analysis.real_convexOn_legendre_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:24:26.853481+00:00
-- url     : https://prove2.me/submissions/aad5f84e-c00f-4a85-bad7-5f9e3027491d

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
import Theorems.Thm_FunctionalInequalities_Analysis_convex_epigraph_legendre_408915f

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
/-- Transfer the actual conjugate's convex epigraph to a real representative.
The finite equality, rather than any global algebraic rule for `toReal`, is used. -/
theorem solution
    (q : E → EReal) (ψ : E → ℝ)
    (hψ : ∀ x, FunctionalInequalities.Analysis.legendre q x = (ψ x : EReal)) :
    ConvexOn ℝ (univ : Set E) ψ := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h : FunctionalInequalities.Analysis.legendre q (a • x + b • y) ≤
      ((a * ψ x + b * ψ y : ℝ) : EReal) :=
    (FunctionalInequalities.Analysis.convex_epigraph_legendre_408915f q)
      (show (x, ψ x) ∈ {p : E × ℝ | FunctionalInequalities.Analysis.legendre q p.1 ≤ (p.2 : EReal)}
        from (hψ x).le)
      (show (y, ψ y) ∈ {p : E × ℝ | FunctionalInequalities.Analysis.legendre q p.1 ≤ (p.2 : EReal)}
        from (hψ y).le)
      ha hb hab
  rw [hψ (a • x + b • y)] at h
  simpa only [smul_eq_mul] using (EReal.coe_le_coe_iff.mp h)

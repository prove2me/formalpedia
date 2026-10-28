-- Prove2me | solution 1 for FunctionalInequalities.Analysis.real_convexOn_legendre_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:34:55.949129+00:00
-- url     : https://prove2.me/submissions/78326da0-c8fa-4da5-a4b8-271a3907fefb

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_BoundedConjugate
import Theorems.Thm_FunctionalInequalities_Analysis_convex_epigraph_legendre_readable

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal Topology RealInnerProductSpace
open FunctionalInequalities
open FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
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
    (FunctionalInequalities.Analysis.convex_epigraph_legendre_readable q)
      (show (x, ψ x) ∈ {p : E × ℝ | FunctionalInequalities.Analysis.legendre q p.1 ≤ (p.2 : EReal)}
        from (hψ x).le)
      (show (y, ψ y) ∈ {p : E × ℝ | FunctionalInequalities.Analysis.legendre q p.1 ≤ (p.2 : EReal)}
        from (hψ y).le)
      ha hb hab
  rw [hψ (a • x + b • y)] at h
  simpa only [smul_eq_mul] using (EReal.coe_le_coe_iff.mp h)

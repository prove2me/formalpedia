-- Prove2me | solution 1 for FunctionalInequalities.Analysis.closedBallCap_lowerSemicontinuous_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:30:00.838985+00:00
-- url     : https://prove2.me/submissions/6222f540-8e06-4f6a-8bc4-732afc2b572c

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_BoundedConjugate

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal Topology RealInnerProductSpace
open FunctionalInequalities
open FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The top sublevel is the whole ambient space; every other sublevel is an
intersection with the closed ball. This helper honestly assumes input LSC. -/
theorem solution
 (φ : E → EReal) (L : NNReal)
    (hφ : LowerSemicontinuous φ) : LowerSemicontinuous (FunctionalInequalities.Analysis.closedBallCap φ L) := by
  classical
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro r
  by_cases hr : r = ⊤
  · subst r
    have hs : FunctionalInequalities.Analysis.closedBallCap φ L ⁻¹' Iic (⊤ : EReal) = (univ : Set E) := by
      ext x
      simp
    rw [hs]
    exact isClosed_univ
  · have hs : FunctionalInequalities.Analysis.closedBallCap φ L ⁻¹' Iic r =
        closedBall (0 : E) (L : ℝ) ∩ (φ ⁻¹' Iic r) := by
      ext x
      by_cases hx : x ∈ closedBall (0 : E) (L : ℝ)
      · simp [FunctionalInequalities.Analysis.closedBallCap, hx]
      · have hnr : ¬ (⊤ : EReal) ≤ r := by
          intro h
          exact hr (top_unique h)
        simp [FunctionalInequalities.Analysis.closedBallCap, hx, hnr]
    rw [hs]
    exact isClosed_closedBall.inter
      (lowerSemicontinuous_iff_isClosed_preimage.mp hφ r)

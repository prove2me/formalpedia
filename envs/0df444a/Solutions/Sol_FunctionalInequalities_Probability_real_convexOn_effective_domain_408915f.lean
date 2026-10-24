-- Prove2me | solution 1 for FunctionalInequalities.Probability.real_convexOn_effective_domain_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:27:18.502816+00:00
-- url     : https://prove2.me/submissions/36f0c3bd-41bc-4c2b-bfa5-ec8786e742f6

import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Order.Compact

open MeasureTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section PointControl
open Set
private lemma FunctionalInequalities.Probability.finite_value_coe {E : Type*} {φ : E → EReal}
    (h0 : ∀ x, 0 ≤ φ x) {x : E} (hx : φ x ≠ ⊤) :
    ((φ x).toReal : EReal) = φ x := by
  exact EReal.coe_toReal hx (ne_of_gt (EReal.bot_lt_zero.trans_le (h0 x)))
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities.Probability in
/-- For a nonnegative extended-real function with convex real epigraph, its real part is convex on the effective domain
`{φ ≠ ⊤}`. -/
lemma solution {φ : E → EReal} (h0 : ∀ x, 0 ≤ φ x)
    (hφ : Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)}) :
    ConvexOn ℝ {x | φ x ≠ ⊤} (fun x => (φ x).toReal) := by
  have hepi : {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)} =
      {p : E × ℝ | p.1 ∈ {x | φ x ≠ ⊤} ∧ (φ p.1).toReal ≤ p.2} := by
    ext p
    constructor
    · intro hp
      change φ p.1 ≤ (p.2 : EReal) at hp
      have hx : φ p.1 ≠ ⊤ := (lt_of_le_of_lt hp (EReal.coe_lt_top p.2)).ne
      refine ⟨hx, ?_⟩
      rw [← finite_value_coe h0 hx] at hp
      exact EReal.coe_le_coe_iff.mp hp
    · rintro ⟨hx, hp⟩
      change φ p.1 ≤ (p.2 : EReal)
      rw [← finite_value_coe h0 hx]
      exact EReal.coe_le_coe_iff.mpr hp
  rw [hepi] at hφ
  exact convexOn_of_convex_epigraph hφ

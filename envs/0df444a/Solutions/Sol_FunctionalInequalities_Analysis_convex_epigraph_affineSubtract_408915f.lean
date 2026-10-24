-- Prove2me | solution 1 for FunctionalInequalities.Analysis.convex_epigraph_affineSubtract_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:13:21.536639+00:00
-- url     : https://prove2.me/submissions/6465c248-c4b0-4f5c-a8d5-376e9fb12195

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Affine
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
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
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- Actual affine subtraction preserves convexity of the real epigraph. -/
theorem solution (f : E → EReal) (a : E) (b : ℝ)
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)}) :
    Convex ℝ {p : E × ℝ | FunctionalInequalities.Analysis.affineSubtract f a b p.1 ≤ (p.2 : EReal)} := by
  intro p hp q hq α β hα hβ hsum
  have hp' : (p.1, p.2 + (inner ℝ a p.1 + b)) ∈ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    change f p.1 ≤ ((p.2 + (inner ℝ a p.1 + b) : ℝ) : EReal)
    have ht := (EReal.sub_le_iff_le_add
      (.inl (EReal.coe_ne_bot (inner ℝ a p.1 + b)))
      (.inl (EReal.coe_ne_top (inner ℝ a p.1 + b)))).mp hp
    simpa only [EReal.coe_add] using ht
  have hq' : (q.1, q.2 + (inner ℝ a q.1 + b)) ∈ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    change f q.1 ≤ ((q.2 + (inner ℝ a q.1 + b) : ℝ) : EReal)
    have ht := (EReal.sub_le_iff_le_add
      (.inl (EReal.coe_ne_bot (inner ℝ a q.1 + b)))
      (.inl (EReal.coe_ne_top (inner ℝ a q.1 + b)))).mp hq
    simpa only [EReal.coe_add] using ht
  have hh := hf hp' hq' hα hβ hsum
  have halg : α * (p.2 + (inner ℝ a p.1 + b)) + β * (q.2 + (inner ℝ a q.1 + b)) =
      α * p.2 + β * q.2 + (inner ℝ a (α • p.1 + β • q.1) + b) := by
    simp only [inner_add_right, inner_smul_right]
    have hb : α * b + β * b = b := by rw [← add_mul, hsum, one_mul]
    nlinarith only [hb]
  change f (α • p.1 + β • q.1) ≤
    ((α * (p.2 + (inner ℝ a p.1 + b)) + β * (q.2 + (inner ℝ a q.1 + b)) : ℝ) : EReal) at hh
  rw [halg] at hh
  change f (α • p.1 + β • q.1) -
    ((inner ℝ a (α • p.1 + β • q.1) + b : ℝ) : EReal) ≤ ((α * p.2 + β * q.2 : ℝ) : EReal)
  apply (EReal.sub_le_iff_le_add
    (.inl (EReal.coe_ne_bot (inner ℝ a (α • p.1 + β • q.1) + b)))
    (.inl (EReal.coe_ne_top (inner ℝ a (α • p.1 + β • q.1) + b)))).mpr
  simpa only [EReal.coe_add] using hh

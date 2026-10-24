-- Prove2me | solution 1 for FunctionalInequalities.Analysis.convex_epigraph_legendre_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:11:40.739983+00:00
-- url     : https://prove2.me/submissions/a445608d-f780-4ac7-b0a6-c9676acf7930

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- The real epigraph of the conjugate is convex for any extended-real input.
The special values in the intercept are handled before real convex combinations. -/
theorem solution (φ : E → EReal) :
    Convex ℝ {p : E × ℝ | FunctionalInequalities.Analysis.legendre φ p.1 ≤ (p.2 : EReal)} := by
  intro p hp q hq a b ha hb hab
  change FunctionalInequalities.Analysis.legendre φ (a • p.1 + b • q.1) ≤ ((a * p.2 + b * q.2 : ℝ) : EReal)
  apply iSup_le
  intro x
  have hp' := (le_iSup (fun z : E => (inner ℝ z p.1 : EReal) - φ z) x).trans hp
  have hq' := (le_iSup (fun z : E => (inner ℝ z q.1 : EReal) - φ z) x).trans hq
  by_cases ht : φ x = ⊤
  · simp only [ht, EReal.sub_top, bot_le]
  by_cases hbot : φ x = ⊥
  · have hbad : (⊤ : EReal) ≤ (p.2 : EReal) := by
      simpa only [hbot, EReal.coe_sub_bot] using hp'
    exact False.elim ((not_le_of_gt (EReal.coe_lt_top p.2)) hbad)
  lift φ x to ℝ using ⟨ht, hbot⟩ with r hr
  have hpReal : inner ℝ x p.1 - r ≤ p.2 := by
    apply EReal.coe_le_coe_iff.mp
    simpa only [← hr, ← EReal.coe_sub] using hp'
  have hqReal : inner ℝ x q.1 - r ≤ q.2 := by
    apply EReal.coe_le_coe_iff.mp
    simpa only [← hr, ← EReal.coe_sub] using hq'
  have hweighted := add_le_add (mul_le_mul_of_nonneg_left hpReal ha)
    (mul_le_mul_of_nonneg_left hqReal hb)
  rw [← EReal.coe_sub]
  apply EReal.coe_le_coe_iff.mpr
  simp only [inner_add_right, inner_smul_right]
  have hprod : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  nlinarith only [hprod, hweighted]

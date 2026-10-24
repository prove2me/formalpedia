-- Prove2me | solution 1 for FunctionalInequalities.Analysis.legendre_ne_bot_iff_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:24:56.114197+00:00
-- url     : https://prove2.me/submissions/8dcecc02-7b4f-4257-8d2e-eab5fae3dc4d

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
/-- Nonemptiness of the primal's effective domain is exactly what excludes
negative infinity in its conjugate. Input values `-∞` need not be ruled out. -/
theorem solution (φ : E → EReal) (y : E) :
    FunctionalInequalities.Analysis.legendre φ y ≠ ⊥ ↔ ∃ x, φ x ≠ ⊤ := by
  constructor
  · intro h
    by_contra hnone
    have htop : ∀ x, φ x = ⊤ := by simpa only [not_exists, not_not] using hnone
    have hbottom : FunctionalInequalities.Analysis.legendre φ y = ⊥ := by simp [FunctionalInequalities.Analysis.legendre, htop]
    exact h hbottom
  · rintro ⟨x, hx⟩
    by_cases hb : φ x = ⊥
    · have htop : FunctionalInequalities.Analysis.legendre φ y = ⊤ := by
        apply eq_top_iff.mpr
        change (⊤ : EReal) ≤ ⨆ z : E, (inner ℝ z y : EReal) - φ z
        simpa only [hb, EReal.coe_sub_bot] using
          (le_iSup (fun z : E => (inner ℝ z y : EReal) - φ z) x)
      simp only [htop, ne_eq, top_ne_bot, not_false_eq_true]
    · lift φ x to ℝ using ⟨hx, hb⟩ with r hr
      have hbound : ((inner ℝ x y - r : ℝ) : EReal) ≤ FunctionalInequalities.Analysis.legendre φ y := by
        change ((inner ℝ x y - r : ℝ) : EReal) ≤
          ⨆ z : E, (inner ℝ z y : EReal) - φ z
        simpa only [← hr, EReal.coe_sub] using
          (le_iSup (fun z : E => (inner ℝ z y : EReal) - φ z) x)
      exact ne_of_gt ((EReal.bot_lt_coe _).trans_le hbound)

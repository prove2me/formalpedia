-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_nonnegative_origin_zero_affine_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:21:31.89146+00:00
-- url     : https://prove2.me/submissions/3770af56-8cdd-46a2-9508-f7b17f0b085f

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
import Theorems.Thm_FunctionalInequalities_Analysis_convex_epigraph_affineSubtract_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_exists_supporting_affine_at_zero_408915f

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
/-- An actual plane touching at0 is produced, then subtracted. No desired
minorant or nonnegative-normalization conclusion is assumed. -/
theorem solution [FiniteDimensional ℝ E]
    (f : E → EReal) (hf : FunctionalInequalities.Analysis.ConvexPotential f)
    (h0 : (0 : E) ∈ interior {x | f x ≠ ⊤}) :
    ∃ a : E, let g := FunctionalInequalities.Analysis.affineSubtract f a (f 0).toReal
      FunctionalInequalities.Analysis.ConvexPotential g ∧ (∀ x, 0 ≤ g x) ∧ g 0 = 0 := by
  obtain ⟨a, ha⟩ := FunctionalInequalities.Analysis.exists_supporting_affine_at_zero_408915f f hf h0
  have hnn : ∀ x, 0 ≤ FunctionalInequalities.Analysis.affineSubtract f a (f 0).toReal x := by
    intro x
    apply (EReal.sub_nonneg (.inr (EReal.coe_ne_top _)) (.inr (EReal.coe_ne_bot _))).mpr
    exact ha x
  refine ⟨a, ⟨?_, FunctionalInequalities.Analysis.convex_epigraph_affineSubtract_408915f f a (f 0).toReal hf.2⟩, hnn, ?_⟩
  · intro x
    exact ne_of_gt (EReal.bot_lt_zero.trans_le (hnn x))
  · change f 0 - ((inner ℝ a 0 + (f 0).toReal : ℝ) : EReal) = 0
    rw [inner_zero_right, zero_add, ← EReal.coe_toReal (interior_subset h0) (hf.1 0),
      ← EReal.coe_sub]
    simp

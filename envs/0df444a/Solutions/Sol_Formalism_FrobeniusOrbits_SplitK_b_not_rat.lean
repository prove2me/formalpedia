-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.SplitK.b_not_rat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:28:02.364834+00:00
-- url     : https://prove2.me/submissions/d9f9a448-b373-4232-8055-6e1540bba7f8

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.SplitK
open Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L] {b : L} {d : ℕ}
namespace Formalism.FrobeniusOrbits.SplitK
theorem _root_.solution (hd : 0 < d) (hb : b ^ 2 = -(d : L)) : b ∉ (⊥ : IntermediateField ℚ L) := by
  intro h
  rw [IntermediateField.mem_bot] at h
  obtain ⟨q, hq⟩ := h
  have key : (algebraMap ℚ L) (q ^ 2) = (algebraMap ℚ L) (-(d : ℚ)) := by
    rw [map_pow, hq, hb, map_neg, map_natCast]
  have h2 : q ^ 2 = -(d : ℚ) := (algebraMap ℚ L).injective key
  have h3 : (0 : ℚ) < d := by exact_mod_cast hd
  nlinarith [sq_nonneg q]
end Formalism.FrobeniusOrbits.SplitK

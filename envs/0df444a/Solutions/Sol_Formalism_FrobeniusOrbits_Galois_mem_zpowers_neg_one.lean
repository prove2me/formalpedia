-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.mem_zpowers_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:00:13.33637+00:00
-- url     : https://prove2.me/submissions/4930a738-1f46-4502-af35-3b836e4d7a26

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Galois
variable {K : Type*} [Field K] {N : ℕ} [NeZero N] {ζ : K}
namespace Formalism.FrobeniusOrbits.Galois
theorem _root_.solution (x : (ZMod N)ˣ) :
    x ∈ Subgroup.zpowers (-1 : (ZMod N)ˣ) ↔ x = 1 ∨ x = -1 := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rcases Int.even_or_odd k with hk | hk
    · exact Or.inl hk.neg_one_zpow
    · exact Or.inr hk.neg_one_zpow
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
end Formalism.FrobeniusOrbits.Galois

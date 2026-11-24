-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.hcl_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:18:08.422808+00:00
-- url     : https://prove2.me/submissions/87c0c833-e969-492a-be7e-35461371e2d5

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_mem_zpowers_neg_one

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
namespace Formalism.FrobeniusOrbits.Galois
theorem _root_.solution (e : ℕ) (u c : (ZMod (2 ^ (e + 2)))ˣ) :
    hcl e u = hcl e c ↔ u = c ∨ u = -c := by
  unfold hcl
  change ((u : (ZMod (2 ^ (e + 2)))ˣ ⧸ Subgroup.zpowers (-1)) = c) ↔ _
  rw [QuotientGroup.eq, mem_zpowers_neg_one, inv_mul_eq_one, inv_mul_eq_iff_eq_mul, mul_neg_one]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      rw [h, neg_neg]
  · rintro (h | h)
    · exact Or.inl h
    · right
      rw [h, neg_neg]
end Formalism.FrobeniusOrbits.Galois

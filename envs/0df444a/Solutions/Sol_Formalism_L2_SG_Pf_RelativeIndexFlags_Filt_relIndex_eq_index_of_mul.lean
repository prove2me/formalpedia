-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.relIndex_eq_index_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:45:57.141666+00:00
-- url     : https://prove2.me/submissions/c6a0dd31-88a3-4b79-9a88-e6cf70352c60

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_RelIndexEqIndexOfMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RelativeIndexFlags Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
variable {G : Type*} [Group G]
namespace Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
theorem _root_.solution (A R : Subgroup G)
    (h : ∀ y : G, ∃ r ∈ R, ∃ a ∈ A, y = r * a) : A.relIndex R = A.index := by
  have hs : MulAction.stabilizer R (((1 : G) : G ⧸ A)) = A.subgroupOf R := by
    ext r
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    change ((((r : G) * 1 : G)) : G ⧸ A) = ((1 : G) : G ⧸ A) ↔ _
    rw [mul_one, QuotientGroup.eq]
    simp
  have ho : MulAction.orbit R (((1 : G) : G ⧸ A)) = Set.univ := by
    ext q
    simp only [Set.mem_univ, iff_true]
    induction q using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨r, hr, a, ha, rfl⟩ := h y
      refine ⟨⟨r, hr⟩, ?_⟩
      change ((((r : G) * 1 : G)) : G ⧸ A) = ((r * a : G) : G ⧸ A)
      rw [mul_one, QuotientGroup.eq]
      simpa using ha
  rw [Subgroup.relIndex, ← hs, MulAction.index_stabilizer, ho, Set.ncard_univ,
    Subgroup.index_eq_card]
end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt

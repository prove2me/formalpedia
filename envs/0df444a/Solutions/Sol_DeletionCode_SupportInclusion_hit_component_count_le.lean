-- Prove2me | solution 1 for DeletionCode.SupportInclusion.hit_component_count_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:14.215172+00:00
-- url     : https://prove2.me/submissions/d3b7a2ea-c2e9-4114-9601-3791c95c19b6

import Definitions.Def_DeletionCode_ComponentBounds
import Definitions.Def_DeletionCode_SupportInclusion
import Theorems.Thm_DeletionCode_SupportInclusion_hit_component_count_le_of_preimages

set_option autoImplicit true
open DeletionCode DeletionCode.SupportInclusion
open SignedSupport SupportComponents RuleSetGraph
namespace DeletionCode.SupportInclusion
theorem _root_.solution {L : ℕ} {Q S : Finset (Gram L → ℤ)}
    (hsub : CoordinateSupportIncluded Q S) (P : RuleSetComponents S → Prop)
    (hhit : ∀ C, P C → ∃ v : RuleSetVertex Q,
      supportComponentMap hsub (Quotient.mk (ruleSetSetoid Q) v) = C) :
    Fintype.card {C : RuleSetComponents S // P C} ≤ componentCount Q := by
  apply hit_component_count_le_of_preimages hsub P
  intro C hC
  obtain ⟨v, hv⟩ := hhit C hC
  exact ⟨Quotient.mk (ruleSetSetoid Q) v, hv⟩
end DeletionCode.SupportInclusion

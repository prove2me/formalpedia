-- Prove2me | solution 1 for Bl.general_b_fact_left_rest.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:55.435232+00:00
-- url     : https://prove2.me/submissions/87fe40d5-9145-4903-820b-35bdec5c05a0

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftRest_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open Bl Bl.general_b_fact_left_rest
namespace Bl.general_b_fact_left_rest
theorem _root_.solution {G T : Type*} [Group G] (N : Subgroup G) (f : G → T) (hs : Function.Surjective f)
    (hf : ∀ a b, f a = f b ↔ a⁻¹ * b ∈ N) : N.index = Nat.card T := by
  show Nat.card (G ⧸ N) = Nat.card T
  refine Nat.card_congr (Equiv.ofBijective (Quotient.lift f ?_) ⟨?_, ?_⟩)
  · intro a b h
    exact (hf a b).2 (QuotientGroup.leftRel_apply.mp h)
  · intro x y h
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    exact QuotientGroup.eq.mpr ((hf a b).1 h)
  · intro t
    obtain ⟨a, rfl⟩ := hs t
    exact ⟨(a : G ⧸ N), rfl⟩
end Bl.general_b_fact_left_rest

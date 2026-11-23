-- Prove2me | solution 1 for CompanionTheory.D.Upq.DoubleCosetLemmas.supp_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:49.074564+00:00
-- url     : https://prove2.me/submissions/0a40e93b-bbca-4ede-9229-3f7901ae86b5

import Mathlib
import Definitions.Def_Development_WeilBound_HeckeVectors_HeckeDoubleCosets_DoubleCosetLemmas_LocCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.DoubleCosetLemmas
variable {G M : Type} [Group G] [MeasurableSpace M]
variable {dx : Measure M} {φ : G → M} {J : Subgroup G} {g : G}
variable {Y : Type} [AddCommGroup Y] [Module ℂ Y] {F : G → Y}
namespace CompanionTheory.D.Upq.DoubleCosetLemmas
theorem _root_.solution (h0 : ∀ z, z ∉ DoubleCoset.doubleCoset g (J : Set G) J → F z = 0) :
    (Function.support fun z : G ⧸ J => F z.out) ⊆ cos J g J := by
  intro z hz
  by_contra hn
  refine hz (h0 _ fun hm => hn ?_)
  obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.1 hm
  exact ⟨a, ha, by rw [← z.out_eq', e]; exact QuotientGroup.mk_mul_of_mem _ hb⟩
end CompanionTheory.D.Upq.DoubleCosetLemmas

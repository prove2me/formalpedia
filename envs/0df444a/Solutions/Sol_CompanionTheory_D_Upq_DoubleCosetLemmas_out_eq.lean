-- Prove2me | solution 1 for CompanionTheory.D.Upq.DoubleCosetLemmas.out_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:24.459675+00:00
-- url     : https://prove2.me/submissions/c75d9309-6bcc-40cc-9047-078ca7c911cc

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
theorem _root_.solution (hR : ∀ z, ∀ k ∈ J, F (z * k) = F z) (x : G) : F ((x : G ⧸ J).out) = F x := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul J x
  rw [hk, hR _ _ k.2]
end CompanionTheory.D.Upq.DoubleCosetLemmas

-- Prove2me | solution 1 for CompanionTheory.D.Upq.DoubleCosetLemmas.Meas.finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:36.228841+00:00
-- url     : https://prove2.me/submissions/eb55a679-d641-486b-9f42-82222f97634f

import Mathlib
import Definitions.Def_Development_WeilBound_HeckeVectors_HeckeDoubleCosets_DoubleCosetLemmas_LocCount
import Theorems.Thm_CompanionTheory_D_Upq_DoubleCosetLemmas_Meas_finset

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
namespace CompanionTheory.D.Upq.DoubleCosetLemmas
namespace Meas
theorem _root_.solution (h : Meas dx φ J g) : (cos J g J).Finite := by
  by_contra hinf
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt h.ne h.fin
  obtain ⟨t, ht, rfl⟩ := Set.Infinite.exists_subset_card_eq hinf n
  rw [← h.finset t ht] at hn
  exact hn.not_ge (measure_mono (image_mono fun x hx => hx.1))
end Meas
end CompanionTheory.D.Upq.DoubleCosetLemmas

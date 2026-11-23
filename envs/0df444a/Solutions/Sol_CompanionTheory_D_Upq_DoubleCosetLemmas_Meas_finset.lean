-- Prove2me | solution 1 for CompanionTheory.D.Upq.DoubleCosetLemmas.Meas.finset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:40.295174+00:00
-- url     : https://prove2.me/submissions/757e2c8f-868a-48eb-8a16-ddf1ab49945e

import Mathlib
import Definitions.Def_Development_WeilBound_HeckeVectors_HeckeDoubleCosets_DoubleCosetLemmas_LocCount
import Theorems.Thm_CompanionTheory_D_Upq_DoubleCosetLemmas_fibre_eq

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
theorem _root_.solution (h : Meas dx φ J g) (t : Finset (G ⧸ J)) (ht : ↑t ⊆ cos J g J) :
    dx (φ '' {x | x ∈ J ∧ ((x * g : G) : G ⧸ J) ∈ t}) = t.card * dx (φ '' stab J g) := by
  have e : φ '' {x | x ∈ J ∧ ((x * g : G) : G ⧸ J) ∈ t} =
      ⋃ z ∈ t, φ '' {x | x ∈ J ∧ ((x * g : G) : G ⧸ J) = z} := by
    ext y; simp only [mem_image, mem_setOf_eq, mem_iUnion]
    exact ⟨fun ⟨x, ⟨h1, h2⟩, h3⟩ => ⟨_, h2, x, ⟨h1, rfl⟩, h3⟩,
      fun ⟨z, hz, x, ⟨h1, h2⟩, h3⟩ => ⟨x, ⟨h1, h2 ▸ hz⟩, h3⟩⟩
  rw [e, measure_biUnion_finset]
  · rw [Finset.sum_congr rfl fun z hz => ?_, Finset.sum_const, nsmul_eq_mul]
    obtain ⟨k, hk, rfl⟩ := ht hz
    rw [fibre_eq hk, h.vol k hk]
  · intro a _ b _ hab
    refine (Set.disjoint_image_iff h.inj).2 (Set.disjoint_left.2 fun x h1 h2 => hab ?_)
    exact h1.2.symm.trans h2.2
  · intro z hz
    obtain ⟨k, hk, rfl⟩ := ht hz
    rw [fibre_eq hk]; exact h.meas k hk
end Meas
end CompanionTheory.D.Upq.DoubleCosetLemmas

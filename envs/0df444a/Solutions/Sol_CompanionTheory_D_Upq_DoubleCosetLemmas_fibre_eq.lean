-- Prove2me | solution 1 for CompanionTheory.D.Upq.DoubleCosetLemmas.fibre_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:57.113846+00:00
-- url     : https://prove2.me/submissions/f1aa5677-ea38-4dea-bd68-f9cbb0948f4a

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
namespace CompanionTheory.D.Upq.DoubleCosetLemmas
theorem _root_.solution {k : G} (hk : k ∈ J) :
    {x | x ∈ J ∧ ((x * g : G) : G ⧸ J) = (k * g : G)} = (k * ·) '' stab J g := by
  ext x
  simp only [mem_setOf_eq, mem_image, stab, QuotientGroup.eq]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨k⁻¹ * x, ⟨J.mul_mem (J.inv_mem hk) hx, ?_⟩, by group⟩
    have := J.inv_mem h
    rwa [show ((x * g)⁻¹ * (k * g))⁻¹ = g⁻¹ * (k⁻¹ * x) * g by group] at this
  · rintro ⟨s, ⟨hs, hs'⟩, rfl⟩
    refine ⟨J.mul_mem hk hs, ?_⟩
    have := J.inv_mem hs'
    rwa [show (g⁻¹ * s * g)⁻¹ = (k * s * g)⁻¹ * (k * g) by group] at this
end CompanionTheory.D.Upq.DoubleCosetLemmas

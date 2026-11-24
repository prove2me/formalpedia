-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_card_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:39:44.452604+00:00
-- url     : https://prove2.me/submissions/c061d153-8077-4f40-a187-ae5ab88d7aa3

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {L : Type} [Field L]
namespace Formalism.UG.P
theorem _root_.solution {G : Type} [Group G] (K : Subgroup G) (d : G) :
    Nat.card {x : G ⧸ K // ∃ a ∈ K, ∃ b ∈ K, x.out = a * d * b} =
      (MulAction.stabilizer K (QuotientGroup.mk d : G ⧸ K)).index := by
  have key : ∀ x : G ⧸ K, (∃ a ∈ K, ∃ b ∈ K, x.out = a * d * b) ↔
      x ∈ MulAction.orbit K (QuotientGroup.mk d : G ⧸ K) := by
    intro x
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨a, ha, b, hb, h⟩
      refine ⟨⟨a, ha⟩, ?_⟩
      have hx : x = QuotientGroup.mk x.out := (QuotientGroup.out_eq' x).symm
      rw [hx, h]
      change (QuotientGroup.mk (a * d) : G ⧸ K) = QuotientGroup.mk (a * d * b)
      rw [QuotientGroup.eq]
      simpa [mul_assoc] using hb
    · rintro ⟨⟨a, ha⟩, h⟩
      change (QuotientGroup.mk (a * d) : G ⧸ K) = x at h
      have h2 : (QuotientGroup.mk (a * d) : G ⧸ K) = QuotientGroup.mk x.out := by
        rw [h, QuotientGroup.out_eq']
      rw [QuotientGroup.eq] at h2
      exact ⟨a, ha, (a * d)⁻¹ * x.out, h2, by rw [← mul_assoc, mul_inv_cancel, one_mul]⟩
  exact Nat.card_congr ((Equiv.subtypeEquivRight key).trans
    (MulAction.orbitEquivQuotientStabilizer K (QuotientGroup.mk d : G ⧸ K)))
end Formalism.UG.P

-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.card_pow_eq_one_le_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:39.921932+00:00
-- url     : https://prove2.me/submissions/87f48517-1073-40e8-83ad-f14c57ffb2f6

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_ResiduesLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Finset
namespace Formalism.GaloisIrreducibility
theorem _root_.solution {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (H : Subgroup G) [IsCyclic H] (hH : H.index ≤ 2) {D : ℕ} (hD : 0 < D) :
    #{a : G | a ^ D = 1} ≤ 2 * D := by
  classical
  set S : Subgroup G := (powMonoidHom D : G →* G).ker with hSdef
  have hmem : ∀ a : G, a ∈ S ↔ a ^ D = 1 := fun a => by simp [hSdef]
  have hcardS : #{a : G | a ^ D = 1} = Nat.card S := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun a => (hmem a).symm))
  rw [hcardS]
  have hK : IsCyclic (H ⊓ S : Subgroup G) := Subgroup.isCyclic_of_le inf_le_left
  have h1 : Nat.card (H ⊓ S : Subgroup G) ≤ D := by
    rw [← IsCyclic.exponent_eq_card]
    apply Nat.le_of_dvd hD
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro g
    have : (g : G) ^ D = 1 := (hmem g).1 g.2.2
    ext; simpa using this
  have h2 : H.relIndex S ≤ 2 := by
    have hd := Subgroup.relIndex_dvd_index_of_normal H S
    have hne : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hd).trans hH
  have h3 : Nat.card (H ⊓ S : Subgroup G) * H.relIndex S = Nat.card S := by
    have := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (H ⊓ S) S bot_le inf_le_right
    rw [Subgroup.inf_relIndex_right, Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left] at this
    exact this
  rw [← h3]
  calc Nat.card (H ⊓ S : Subgroup G) * H.relIndex S ≤ D * 2 := Nat.mul_le_mul h1 h2
    _ = 2 * D := by ring
end Formalism.GaloisIrreducibility

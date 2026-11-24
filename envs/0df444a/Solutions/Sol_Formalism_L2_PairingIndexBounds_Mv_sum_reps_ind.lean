-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Mv.sum_reps_ind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:14:09.899061+00:00
-- url     : https://prove2.me/submissions/a1d12cd5-4b84-4a44-971a-1114ecd498d6

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_FourierTransformIdentityHolds
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_ind_of_mem
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_ind_of_not_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.PairingIndexBounds Formalism.L2.PairingIndexBounds.Mv
variable {k : Type*} [Field k] {A B T : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup T] [Module k T]
namespace Formalism.L2.PairingIndexBounds.Mv
theorem _root_.solution {G : Type*} [AddCommGroup G] (M N : AddSubgroup G) (S : Finset G) (hS : IsRepsG M N S) (t : G) :
    ∑ a ∈ S, ind (k := k) (M : Set G) (t + a) * ind (k := k) (N : Set G) (t + a) = ind (k := k) (N : Set G) t := by
  obtain ⟨hSN, hSinj, hSsurj⟩ := hS
  by_cases ht : t ∈ N
  · obtain ⟨x, hxS, hx⟩ := hSsurj (-t) (N.neg_mem ht)
    have hxM : t + x ∈ M := by
      have := M.neg_mem hx
      have e : -(-t - x) = t + x := by abel
      rwa [e] at this
    rw [Finset.sum_eq_single x]
    · rw [ind_of_mem (show t + x ∈ (M : Set G) from hxM),
        ind_of_mem (show t + x ∈ (N : Set G) from N.add_mem ht (hSN x hxS)),
        ind_of_mem (show t ∈ (N : Set G) from ht), one_mul]
    · intro a haS hax
      have : t + a ∉ (M : Set G) := by
        intro h
        apply hax
        apply hSinj a haS x hxS
        have := M.add_mem h hx
        have e : t + a + (-t - x) = a - x := by abel
        rwa [e] at this
      rw [ind_of_not_mem this, zero_mul]
    · intro h; exact absurd hxS h
  · rw [ind_of_not_mem (show t ∉ (N : Set G) from ht)]
    apply Finset.sum_eq_zero
    intro a ha
    have : t + a ∉ (N : Set G) := by
      intro h
      apply ht
      have := N.sub_mem h (hSN a ha)
      rwa [add_sub_cancel_right] at this
    rw [ind_of_not_mem this, mul_zero]
end Formalism.L2.PairingIndexBounds.Mv

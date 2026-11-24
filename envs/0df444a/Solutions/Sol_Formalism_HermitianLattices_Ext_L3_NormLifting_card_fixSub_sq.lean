-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.NormLifting.card_fixSub_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:16.275988+00:00
-- url     : https://prove2.me/submissions/cb947084-f06f-4306-ad1f-809eac5d881e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_card_fiber_mul_card_range
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_mem_fixSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_map_inv_eq_neg
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_range_trI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.NormLifting
variable {A : Type*} [CommRing A] (σ : A →+* A) (I : Ideal A)
variable {σ I}
namespace Formalism.HermitianLattices.Ext.L3.NormLifting
theorem _root_.solution (hσ : ∀ a, σ (σ a) = a) (hI : ∀ a ∈ I, σ a ∈ I) {θ e : A}
    (he : (θ - σ θ) * e = 1) : Nat.card (fixSub σ I) ^ 2 = Nat.card I := by

  have hδ : σ (θ - σ θ) = -(θ - σ θ) := by
    rw [map_sub, hσ]
    ring
  have he' := map_inv_eq_neg hσ he
  have h1 := card_fiber_mul_card_range (trI σ I) 0 (zero_mem _)
  rw [range_trI hσ hI he] at h1
  have e1 : {w : I // trI σ I w = 0} ≃ fixSub σ I :=
    { toFun := fun w => ⟨e * (w.1 : A), (mem_fixSub σ I).mpr ⟨I.mul_mem_left _ w.1.2, by
          have hw : (w.1 : A) + σ (w.1 : A) = 0 := w.2
          rw [map_mul, he']
          linear_combination (-e) * hw⟩⟩
      invFun := fun x => ⟨⟨(θ - σ θ) * (x : A), I.mul_mem_left _ ((mem_fixSub σ I).mp x.2).1⟩, by
          show (θ - σ θ) * (x : A) + σ ((θ - σ θ) * (x : A)) = 0
          rw [map_mul, hδ, ((mem_fixSub σ I).mp x.2).2]
          ring⟩
      left_inv := fun w => by
        apply Subtype.ext
        apply Subtype.ext
        show (θ - σ θ) * (e * (w.1 : A)) = w.1
        rw [← mul_assoc, he, one_mul]
      right_inv := fun x => by
        apply Subtype.ext
        show e * ((θ - σ θ) * (x : A)) = x
        rw [← mul_assoc, mul_comm e, he, one_mul] }
  rw [Nat.card_congr e1] at h1
  rw [sq]
  exact h1
end Formalism.HermitianLattices.Ext.L3.NormLifting

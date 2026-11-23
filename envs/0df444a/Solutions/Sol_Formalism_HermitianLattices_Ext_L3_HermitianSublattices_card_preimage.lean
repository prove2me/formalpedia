-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HermitianSublattices.card_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:52:02.53852+00:00
-- url     : https://prove2.me/submissions/ec496e11-17e0-4981-9ca4-d0a43c9ad413

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HermitianSublattices
open Matrix
variable {A Z : Type*} [AddCommGroup A] [AddCommGroup Z]
namespace Formalism.HermitianLattices.Ext.L3.HermitianSublattices
theorem _root_.solution [Finite A] (f : A →+ Z) (hf : Function.Surjective f) (T : Z → Prop) :
    Nat.card {a // T (f a)} = Nat.card f.ker * Nat.card {z // T z} := by
  classical
  choose s hs using hf
  let e : {a // T (f a)} ≃ f.ker × {z // T z} :=
  { toFun := fun a => (⟨a.1 - s (f a.1), by rw [AddMonoidHom.mem_ker, map_sub, hs, sub_self]⟩,
      ⟨f a.1, a.2⟩)
    invFun := fun x => ⟨x.1.1 + s x.2.1, by
      rw [map_add, AddMonoidHom.mem_ker.mp x.1.2, hs, zero_add]
      exact x.2.2⟩
    left_inv := fun a => by
      apply Subtype.ext
      show a.1 - s (f a.1) + s (f a.1) = a.1
      exact sub_add_cancel _ _
    right_inv := by
      rintro ⟨⟨k, hk⟩, ⟨z, hz⟩⟩
      have hfk : f (k + s z) = z := by rw [map_add, AddMonoidHom.mem_ker.mp hk, hs, zero_add]
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · show k + s z - s (f (k + s z)) = k
        rw [hfk, add_sub_cancel_right]
      · show f (k + s z) = z
        exact hfk }
  rw [Nat.card_congr e, Nat.card_prod]
end Formalism.HermitianLattices.Ext.L3.HermitianSublattices

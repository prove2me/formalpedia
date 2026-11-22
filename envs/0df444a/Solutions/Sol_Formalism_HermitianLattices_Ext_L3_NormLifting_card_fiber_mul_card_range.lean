-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.NormLifting.card_fiber_mul_card_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:28:15.907986+00:00
-- url     : https://prove2.me/submissions/4990dd34-c974-4c4c-b887-2f21eaa39b64

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.NormLifting
namespace Formalism.HermitianLattices.Ext.L3.NormLifting
theorem _root_.solution {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) (h : H) (hh : h ∈ f.range) :
    Nat.card {g : G // f g = h} * Nat.card f.range = Nat.card G := by

  obtain ⟨g0, hg0⟩ := hh
  have e1 : {g : G // f g = h} ≃ f.ker :=
    { toFun := fun g => ⟨g.1 - g0, by rw [AddMonoidHom.mem_ker, map_sub, g.2, hg0, sub_self]⟩
      invFun := fun k => ⟨k.1 + g0, by rw [map_add, (AddMonoidHom.mem_ker).mp k.2, hg0, zero_add]⟩
      left_inv := fun g => by ext; simp
      right_inv := fun k => by ext; simp }
  rw [Nat.card_congr e1, ← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv, mul_comm]
  exact (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker).symm
end Formalism.HermitianLattices.Ext.L3.NormLifting

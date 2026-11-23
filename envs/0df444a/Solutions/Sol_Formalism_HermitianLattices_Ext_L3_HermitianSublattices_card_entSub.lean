-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HermitianSublattices.card_entSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:50:15.237826+00:00
-- url     : https://prove2.me/submissions/fa835e95-ca6c-4859-adb7-cf6c7b9b61d1

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_mem_entSub

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
variable {A A' : Type*} [CommRing A] [StarRing A] [CommRing A'] [StarRing A']
variable {m r : Type*} [Fintype m] [Fintype r] [DecidableEq m] [DecidableEq r]
namespace Formalism.HermitianLattices.Ext.L3.HermitianSublattices
theorem _root_.solution (J : Ideal A) :
    Nat.card (entSub m r J) = Nat.card J ^ (Fintype.card m * Fintype.card r) := by
  classical
  let e : entSub m r J ≃ (m → r → J) :=
  { toFun := fun Y i j => ⟨Y.1 i j, mem_entSub.mp Y.2 i j⟩
    invFun := fun Y => ⟨fun i j => (Y i j : A), mem_entSub.mpr fun i j => (Y i j).2⟩
    left_inv := fun Y => rfl
    right_inv := fun Y => rfl }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := m),
    Nat.card_eq_fintype_card (α := r), ← pow_mul, mul_comm]
end Formalism.HermitianLattices.Ext.L3.HermitianSublattices

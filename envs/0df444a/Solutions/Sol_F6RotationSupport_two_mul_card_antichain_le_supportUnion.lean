-- Prove2me | solution 1 for F6RotationSupport.two_mul_card_antichain_le_supportUnion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:23:01.289353+00:00
-- url     : https://prove2.me/submissions/0aa73491-895a-4052-95c0-a3d30b2748b0

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
import Theorems.Thm_F6RotationSupport_mem_supportUnion
import Theorems.Thm_F6RotationSupport_mem_interval
import Theorems.Thm_F6RotationSupport_mem_commonInc
import Theorems.Thm_F6RotationSupport_card_supportUnion_antichain
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_mem_part
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_mem_ideal
attribute [local simp] F6ConvexWindow.ChainDecomposition.mem_part
attribute [local simp] F6ConvexWindow.mem_Inc
attribute [local simp] F6ConvexWindow.mem_antichains
attribute [local simp] F6ConvexWindow.mem_ideal


attribute [local simp] F6RotationSupport.mem_supportUnion
attribute [local simp] F6RotationSupport.mem_interval
attribute [local simp] F6RotationSupport.mem_commonInc

set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]
namespace F6RotationSupport
theorem _root_.solution (supp : R → Finset M)
    (HMIN : ∀ rho : R, 2 ≤ (supp rho).card)
    (HSHARE : ∀ rho sigma : R, (supp rho ∩ supp sigma).Nonempty →
      rho ≤ sigma ∨ sigma ≤ rho)
    {A : Finset R} (hA : F6ConvexWindow.Antichain A) :
    2 * A.card ≤ (supportUnion supp A).card := by
  rw [card_supportUnion_antichain supp HSHARE hA]
  calc
    2 * A.card = ∑ _rho ∈ A, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ rho ∈ A, (supp rho).card := Finset.sum_le_sum (fun rho _ => HMIN rho)
end F6RotationSupport

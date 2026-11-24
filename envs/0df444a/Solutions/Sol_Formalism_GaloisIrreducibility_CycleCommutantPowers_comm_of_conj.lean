-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.CycleCommutantPowers.comm_of_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:02.799915+00:00
-- url     : https://prove2.me/submissions/0db9fca3-6b9d-44b1-b510-9a904133f549

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_JordanPrime
import Theorems.Thm_Formalism_GaloisIrreducibility_CycleCommutantPowers_conj_inv_exists
import Theorems.Thm_Formalism_GaloisIrreducibility_CycleCommutantPowers_conj_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Equiv Equiv.Perm MulAction
open Formalism.GaloisIrreducibility.CycleCommutantPowers
variable {α : Type} [Fintype α] [DecidableEq α]
namespace Formalism.GaloisIrreducibility.CycleCommutantPowers
theorem _root_.solution (x y g : Perm α) (u w : ℤ) (hx : x * g * x⁻¹ = g ^ u)
    (hy : y * g * y⁻¹ = g ^ w) :
    (x * y * x⁻¹ * y⁻¹) * g * (x * y * x⁻¹ * y⁻¹)⁻¹ = g := by
  obtain ⟨v, hv0⟩ := conj_inv_exists x g u hx
  obtain ⟨v', hw0⟩ := conj_inv_exists y g w hy
  have hv : x⁻¹ * g * x = g ^ v := by rw [inv_inv] at hv0; exact hv0
  have hw : y⁻¹ * g * y = g ^ v' := by rw [inv_inv] at hw0; exact hw0
  have huv : g ^ (u * v) = g := by
    rw [← conj_key x g u hx v, ← hv]
    first | group | simp [mul_assoc]
  have hwv : g ^ (w * v') = g := by
    rw [← conj_key y g w hy v', ← hw]
    first | group | simp [mul_assoc]
  have k1 := conj_key x⁻¹ g v hv0 v'
  rw [inv_inv] at k1
  have e1 : (x * y * x⁻¹ * y⁻¹) * g * (x * y * x⁻¹ * y⁻¹)⁻¹ =
      x * (y * (x⁻¹ * (y⁻¹ * g * y) * x) * y⁻¹) * x⁻¹ := by
    first | group | simp only [mul_inv_rev, inv_inv, mul_assoc]
  rw [e1, hw, k1, conj_key y g w hy (v * v'), conj_key x g u hx (w * (v * v'))]
  have he : u * (w * (v * v')) = (u * v) * (w * v') := by ring
  rw [he, zpow_mul, huv, hwv]
end Formalism.GaloisIrreducibility.CycleCommutantPowers

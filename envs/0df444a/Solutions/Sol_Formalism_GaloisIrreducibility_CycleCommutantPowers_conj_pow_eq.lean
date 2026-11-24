-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.CycleCommutantPowers.conj_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:18.769739+00:00
-- url     : https://prove2.me/submissions/825e7e0b-2c61-432f-985c-f3ec8638ba0d

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_JordanPrime

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
theorem _root_.solution (x g : Perm α) (u : ℤ) (hx : x * g * x⁻¹ = g ^ u) :
    ∀ n : ℕ, x ^ n * g * (x ^ n)⁻¹ = g ^ (u ^ n) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have key : x ^ n * g ^ u * (x ^ n)⁻¹ = (x ^ n * g * (x ^ n)⁻¹) ^ u := by
      have h := map_zpow (MulAut.conj (x ^ n)) g u
      simpa only [MulAut.conj_apply] using h
    calc x ^ (n + 1) * g * (x ^ (n + 1))⁻¹ = x ^ n * (x * g * x⁻¹) * (x ^ n)⁻¹ := by
          first
            | (rw [pow_succ, mul_inv_rev]; simp only [mul_assoc])
            | group
      _ = x ^ n * g ^ u * (x ^ n)⁻¹ := by rw [hx]
      _ = (x ^ n * g * (x ^ n)⁻¹) ^ u := key
      _ = (g ^ (u ^ n)) ^ u := by rw [ih]
      _ = g ^ (u ^ (n + 1)) := by rw [pow_succ, zpow_mul]
end Formalism.GaloisIrreducibility.CycleCommutantPowers

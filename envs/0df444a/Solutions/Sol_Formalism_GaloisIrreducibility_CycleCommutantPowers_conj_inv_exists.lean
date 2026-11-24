-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.CycleCommutantPowers.conj_inv_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:53.674812+00:00
-- url     : https://prove2.me/submissions/55bdc0d0-dc0d-4f9b-9160-2bb8a45d356b

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_JordanPrime
import Theorems.Thm_Formalism_GaloisIrreducibility_CycleCommutantPowers_conj_pow_eq

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
    ∃ v : ℤ, x⁻¹ * g * x⁻¹⁻¹ = g ^ v := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, x ^ (k + 1) = 1 :=
    ⟨orderOf x - 1, by rw [Nat.sub_add_cancel (orderOf_pos x)]; exact pow_orderOf_eq_one x⟩
  have hinv : x⁻¹ = x ^ k := by
    rw [pow_succ] at hk
    exact (eq_inv_of_mul_eq_one_left hk).symm
  refine ⟨u ^ k, ?_⟩
  rw [hinv]
  exact conj_pow_eq x g u hx k
end Formalism.GaloisIrreducibility.CycleCommutantPowers

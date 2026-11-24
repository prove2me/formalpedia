-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.CycleCommutantPowers.eq_zpow_on_support
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:12.85525+00:00
-- url     : https://prove2.me/submissions/4ea7f80b-941c-4a14-8e60-47ac9e537fc6

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
theorem _root_.solution (g z : Perm α) (hg : g.IsCycle) (hz : z * g = g * z) :
    ∃ j : ℤ, ∀ d, g d ≠ d → z d = (g ^ j) d := by
  obtain ⟨a, ha, hcyc⟩ := hg
  have hza : g (z a) ≠ z a := by
    intro h
    apply ha
    apply z.injective
    have h2 : (z * g) a = (g * z) a := by rw [hz]
    simp only [Perm.mul_apply] at h2
    rw [h2, h]
  obtain ⟨j, hj⟩ := hcyc hza
  refine ⟨j, fun d hd => ?_⟩
  obtain ⟨i, rfl⟩ := hcyc hd
  have hcomm : z * g ^ i = g ^ i * z := ((show Commute z g from hz).zpow_right i).eq
  calc z ((g ^ i) a) = (z * g ^ i) a := rfl
    _ = (g ^ i * z) a := by rw [hcomm]
    _ = (g ^ i) (z a) := rfl
    _ = (g ^ i) ((g ^ j) a) := by rw [hj]
    _ = (g ^ i * g ^ j) a := rfl
    _ = (g ^ j * g ^ i) a := by rw [← zpow_add, ← zpow_add, add_comm]
    _ = (g ^ j) ((g ^ i) a) := rfl
end Formalism.GaloisIrreducibility.CycleCommutantPowers

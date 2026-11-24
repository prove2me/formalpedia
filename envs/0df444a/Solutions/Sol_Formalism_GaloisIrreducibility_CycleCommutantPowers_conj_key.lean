-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.CycleCommutantPowers.conj_key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:33.538053+00:00
-- url     : https://prove2.me/submissions/532fe394-47aa-4bbc-8d71-cb9bbbec9404

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
theorem _root_.solution (c g : Perm α) (e : ℤ) (hc : c * g * c⁻¹ = g ^ e) (m : ℤ) :
    c * g ^ m * c⁻¹ = g ^ (e * m) := by
  have h := map_zpow (MulAut.conj c) g m
  simp only [MulAut.conj_apply] at h
  rw [h, hc, ← zpow_mul]
end Formalism.GaloisIrreducibility.CycleCommutantPowers

-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.BorderedIndexCases.bord_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:32.920174+00:00
-- url     : https://prove2.me/submissions/e97bb5a6-2dbc-469b-bbd1-69fdfda621e7

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OneNonUnit
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_mul
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ'
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ

set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Matrix
open Formalism.GaloisIrreducibility.BorderedIndexCases
variable {R : Type} [CommRing R]
namespace Formalism.GaloisIrreducibility.BorderedIndexCases
theorem _root_.solution {m : ℕ} {M : Matrix (Fin m) (Fin m) R} (h : IsUnit M) : IsUnit (bord M) := by
  obtain ⟨u, rfl⟩ := h
  refine ⟨⟨bord (u : Matrix (Fin m) (Fin m) R), bord (↑u⁻¹ : Matrix (Fin m) (Fin m) R), ?_, ?_⟩, rfl⟩
  · first
    | rw [bord_mul, Units.mul_inv, bord_one]
    | simp [bord_mul, bord_one]
  · first
    | rw [bord_mul, Units.inv_mul, bord_one]
    | simp [bord_mul, bord_one]
end Formalism.GaloisIrreducibility.BorderedIndexCases

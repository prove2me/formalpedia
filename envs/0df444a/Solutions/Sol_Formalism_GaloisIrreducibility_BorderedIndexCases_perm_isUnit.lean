-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.BorderedIndexCases.perm_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:33.619866+00:00
-- url     : https://prove2.me/submissions/57e32946-d2fb-4100-8eeb-797319fdda16

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OneNonUnit
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
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
open Matrix
open Formalism.GaloisIrreducibility.BorderedIndexCases
variable {R : Type} [CommRing R]
namespace Formalism.GaloisIrreducibility.BorderedIndexCases
theorem _root_.solution {s : ℕ} (σ : Equiv.Perm (Fin s)) :
    IsUnit (σ.toPEquiv.toMatrix : Matrix (Fin s) (Fin s) R) := by
  refine ⟨⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix, ?_, ?_⟩, rfl⟩
  · first
    | rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
        Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
    | simp [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
  · first
    | rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
        Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
    | simp [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
end Formalism.GaloisIrreducibility.BorderedIndexCases

-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.BorderedIndexCases.equi_submatrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:32.912588+00:00
-- url     : https://prove2.me/submissions/5dbd3b1a-d1d6-46f8-a492-07d70dd336cf

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OneNonUnit
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_perm_isUnit
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
theorem _root_.solution {s : ℕ} (A : Matrix (Fin s) (Fin s) R) (σ τ : Equiv.Perm (Fin s)) :
    Equi A (A.submatrix σ τ) := by
  unfold Equi
  refine ⟨σ.toPEquiv.toMatrix, τ.symm.toPEquiv.toMatrix, perm_isUnit σ, perm_isUnit τ.symm, ?_⟩
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp
end Formalism.GaloisIrreducibility.BorderedIndexCases

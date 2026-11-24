-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.BorderedIndexCases.Equi.rank_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:32.683002+00:00
-- url     : https://prove2.me/submissions/21c0bc74-40a7-46cf-825a-5e347f7d8aa9

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
namespace Equi
theorem _root_.solution {K : Type} [Field K] (φ : R →+* K) {s : ℕ}
    {A B : Matrix (Fin s) (Fin s) R} (h : Equi A B) : (B.map φ).rank = (A.map φ).rank := by
  unfold Equi at h
  obtain ⟨P, Q, hP, hQ, rfl⟩ := h
  have hP' : IsUnit (P.map φ).det := by
    rw [← Matrix.isUnit_iff_isUnit_det]; simpa using hP.map φ.mapMatrix
  have hQ' : IsUnit (Q.map φ).det := by
    rw [← Matrix.isUnit_iff_isUnit_det]; simpa using hQ.map φ.mapMatrix
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQ',
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hP']
end Equi
end Formalism.GaloisIrreducibility.BorderedIndexCases

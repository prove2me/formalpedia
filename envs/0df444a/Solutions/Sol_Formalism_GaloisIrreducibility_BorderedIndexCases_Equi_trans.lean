-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.BorderedIndexCases.Equi.trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:48:55.327639+00:00
-- url     : https://prove2.me/submissions/c0dffcd6-9813-48db-8555-216645b16b21

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
theorem _root_.solution {s : ℕ} {A B C : Matrix (Fin s) (Fin s) R} (h1 : Equi A B) (h2 : Equi B C) :
    Equi A C := by
  unfold Equi at h1 h2 ⊢
  obtain ⟨P1, Q1, hP1, hQ1, rfl⟩ := h1
  obtain ⟨P2, Q2, hP2, hQ2, rfl⟩ := h2
  exact ⟨P2 * P1, Q1 * Q2, hP2.mul hP1, hQ1.mul hQ2, by simp only [Matrix.mul_assoc]⟩
end Equi
end Formalism.GaloisIrreducibility.BorderedIndexCases

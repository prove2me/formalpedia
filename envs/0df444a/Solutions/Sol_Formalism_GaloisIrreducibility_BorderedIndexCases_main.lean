-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.BorderedIndexCases.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:59:43.326712+00:00
-- url     : https://prove2.me/submissions/669d14a2-b7e4-47c9-9a19-cede4f7d9969

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OneNonUnit
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_mul
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_isUnit
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_diag
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_map
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_rank_bord_le
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_rank_map
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_equi_submatrix
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_clear
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
open Matrix
open Formalism.GaloisIrreducibility.BorderedIndexCases
variable {R : Type} [CommRing R] [IsLocalRing R]
namespace Formalism.GaloisIrreducibility.BorderedIndexCases
theorem _root_.solution (n : ℕ) : ∀ (A : Matrix (Fin (n+1)) (Fin (n+1)) R),
    n ≤ (A.map (IsLocalRing.residue R)).rank →
    ∃ d : R, Equi A (diagonal fun i : Fin (n+1) => if (i : ℕ) = n then d else 1) := by
  induction n with
  | zero =>
    intro A _
    refine ⟨A 0 0, ?_⟩
    unfold Equi
    refine ⟨1, 1, isUnit_one, isUnit_one, ?_⟩
    ext i j
    fin_cases i; fin_cases j
    simp
  | succ n ih =>
    intro A hA
    obtain ⟨i, j, hij⟩ : ∃ i j, IsUnit (A i j) := by
      by_contra hne
      push_neg at hne
      have h0 : A.map (IsLocalRing.residue R) = 0 := by
        ext i j
        simp only [Matrix.map_apply, Matrix.zero_apply]
        exact (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr (hne i j))
      rw [h0, Matrix.rank_zero] at hA
      omega
    have hu : IsUnit ((A.submatrix (Equiv.swap 0 i) (Equiv.swap 0 j)) 0 0) := by
      simpa using hij
    obtain ⟨A', e2⟩ := clear _ hu
    have e12 : Equi A (bord A') := (equi_submatrix A _ _).trans e2
    have hr : n ≤ (A'.map (IsLocalRing.residue R)).rank := by
      have h1 := e12.rank_map (IsLocalRing.residue R)
      have h2 := rank_bord_le (A'.map (IsLocalRing.residue R))
      rw [← bord_map, h1] at h2
      omega
    obtain ⟨d, hd⟩ := ih A' hr
    unfold Equi at hd
    obtain ⟨P, Q, hP, hQ, hPQ⟩ := hd
    refine ⟨d, e12.trans ?_⟩
    unfold Equi
    refine ⟨bord P, bord Q, bord_isUnit hP, bord_isUnit hQ, ?_⟩
    rw [bord_mul, bord_mul, hPQ, bord_diag]
end Formalism.GaloisIrreducibility.BorderedIndexCases

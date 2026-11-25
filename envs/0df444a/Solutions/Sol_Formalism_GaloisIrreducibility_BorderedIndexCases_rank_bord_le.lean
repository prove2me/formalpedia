-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.BorderedIndexCases.rank_bord_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:50:13.541209+00:00
-- url     : https://prove2.me/submissions/91e3f364-9ec2-4bee-9e38-4df618ba6330

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OneNonUnit
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_rank_add_le__855d90caba7d
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
theorem _root_.solution {K : Type} [Field K] {m : ℕ} (M : Matrix (Fin m) (Fin m) K) :
    (bord M).rank ≤ M.rank + 1 := by
  classical
  let S : Matrix (Fin (m+1)) (Fin m) K := Matrix.of fun i k => if i = k.succ then 1 else 0
  let T : Matrix (Fin m) (Fin (m+1)) K := Matrix.of fun k j => if j = k.succ then 1 else 0
  let S' : Matrix (Fin (m+1)) (Fin 1) K := Matrix.of fun i _ => if i = 0 then 1 else 0
  let T' : Matrix (Fin 1) (Fin (m+1)) K := Matrix.of fun _ j => if j = 0 then 1 else 0
  have hsplit : bord M = S' * T' + S * M * T := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [S, T, S', T', Matrix.mul_apply, Fin.sum_univ_succ]
  rw [hsplit]
  refine (rank_add_le' _ _).trans ?_
  have h1 : (S' * T').rank ≤ 1 :=
    (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width S')
  have h2 : (S * M * T).rank ≤ M.rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  omega
end Formalism.GaloisIrreducibility.BorderedIndexCases

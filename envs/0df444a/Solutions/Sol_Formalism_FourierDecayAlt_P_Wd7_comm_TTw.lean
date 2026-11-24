-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.comm_TTw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:12.347197+00:00
-- url     : https://prove2.me/submissions/17d943cc-9553-40e3-b580-e6bf66e65b9f

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_io_comm_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_scalar_commute_R_matrix_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_scalar_commute_transposed_R_matrix_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_commute_matrix_mul_entry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd7
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd7
theorem _root_.solution (QQ : K → M2 A) (w : List (Letter K S)) (z : A)
    (hz : ∀ Y i j, Commute z (QQ Y i j)) (Y : K) (i j : Fin 2) :
    Commute (io z : SlopeTestRemainingChoices S A) (TTw QQ w Y i j) := by
  induction w generalizing i j with
  | nil => exact io_comm_io (hz Y i j)
  | cons l w ih =>
    by_cases h : l.plus
    · rw [show TTw QQ (l :: w) Y = TTw QQ w Y * Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) from by simp [TTw, h]]
      exact commute_matrix_mul_entry ih (scalar_commute_R_matrix_entry _ _ z) i j
    · rw [show TTw QQ (l :: w) Y = Rht0 l.intersection_update_fsHerm_neg_one (l.pt - Y) * TTw QQ w Y from by simp [TTw, h]]
      exact commute_matrix_mul_entry (scalar_commute_transposed_R_matrix_entry _ _ z) ih i j
end Formalism.FourierDecayAlt.P.Wd7

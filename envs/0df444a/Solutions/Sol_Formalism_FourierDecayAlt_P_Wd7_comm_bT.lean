-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.comm_bT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:31.766417+00:00
-- url     : https://prove2.me/submissions/a72bc4bc-478b-40a0-acb7-b8ad299e172e

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_ins_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_io_comm_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_free_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_commute_Avr_Bvr_of_commute_siteOps
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_comm_Tstar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_mem_ops_hol
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_mem_ops_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_commute_Avr_Bvr_of_commute_siteOps
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_ins_comm


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
theorem _root_.solution (σ : Site A) (w : List (Letter K S)) (z : A) (hz : ∀ x ∈ ops σ, Commute z x) :
    Commute (io z : SlopeTestRemainingChoices S A) (bT σ w) := by
  induction w with
  | nil => exact Commute.one_right _
  | cons l w ih =>
    simp only [bT, vlet]
    refine Commute.mul_right (ins_comm _ _ _ (free_io _ _) fun i j => ?_) ih
    split_ifs
    · exact io_comm_io (commute_Avr_Bvr_of_commute_siteOps σ l.pt z (fun x hx => hz x (mem_ops_hol hx)) i j)
    · exact io_comm_io (comm_Tstar σ l.pt z (fun x hx => hz _ (mem_ops_star hx)) i j)
end Formalism.FourierDecayAlt.P.Wd7

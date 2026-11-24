-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.free_bT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:42.591329+00:00
-- url     : https://prove2.me/submissions/db172afa-4009-4901-86fb-809e8aaf5dcc

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_free_vlet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd8
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd8
theorem _root_.solution (σ : Site A) (w : List (Letter K S)) {a : S} (ha : a ∉ w.map Letter.intersection_update_fsHerm_neg_one)
    (i j : Fin 2) : Commute (eU a i j : SlopeTestRemainingChoices S A) (bT σ w) := by
  induction w with
  | nil =>
    simp only [bT]
    exact Commute.one_right _
  | cons l w ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at ha
    simp only [bT]
    exact (free_vlet σ l ha.1 i j).mul_right (ih ha.2)
end Formalism.FourierDecayAlt.P.Wd8

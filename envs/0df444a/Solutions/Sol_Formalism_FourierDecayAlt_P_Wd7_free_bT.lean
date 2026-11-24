-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.free_bT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:45.411542+00:00
-- url     : https://prove2.me/submissions/17bf44d4-2a2a-4b45-9315-a2315029eb57

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_ins_free
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_free_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_free_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_freeOf2_lift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_ins_free


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
theorem _root_.solution {c : S} (σ : Site A) (w : List (Letter K S)) (hc : c ∉ w.map Letter.intersection_update_fsHerm_neg_one) :
    FreeOf c (bT σ w) := by
  induction w with
  | nil => exact free_one c
  | cons l w ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hc
    simp only [bT, vlet]
    exact free_mul (ins_free hc.1 _ (freeOf2_lift c _)) (ih hc.2)
end Formalism.FourierDecayAlt.P.Wd7

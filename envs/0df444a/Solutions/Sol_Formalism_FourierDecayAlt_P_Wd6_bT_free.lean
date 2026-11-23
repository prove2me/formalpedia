-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.bT_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:34.590812+00:00
-- url     : https://prove2.me/submissions/dc4c336e-4ae8-43c9-9e69-d6235e0e7873

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_vlet_free

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd6
theorem _root_.solution (σ : Site A) (w : List (Letter K S)) {a : S} (h : a ∉ w.map Letter.intersection_update_fsHerm_neg_one) :
    FreeOf a (bT σ w) := by
  induction w with
  | nil => exact fun i j => Commute.one_right _
  | cons l w ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    exact fun i j => (vlet_free σ l h.1 i j).mul_right (ih h.2 i j)
end Formalism.FourierDecayAlt.P.Wd6

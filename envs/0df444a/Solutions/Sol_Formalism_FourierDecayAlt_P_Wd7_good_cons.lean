-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.good_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:08.464366+00:00
-- url     : https://prove2.me/submissions/8efb09e8-3178-468c-9569-94ee6fea2dc4

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry

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
theorem _root_.solution {l : Letter K S} {w : List (Letter K S)} (h : Good (l :: w)) :
    Good w ∧ l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one ∧ star l.pt = l.pt ∧ Reg w l.pt := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [List.map_cons, List.nodup_cons] at h1
  rw [List.pairwise_cons] at h3
  exact ⟨⟨h1.2, fun l' hl' => h2 l' (List.mem_cons_of_mem _ hl'), h3.2⟩, h1.1,
    h2 l List.mem_cons_self, h3.1⟩
end Formalism.FourierDecayAlt.P.Wd7

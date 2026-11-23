-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd10.good_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:41.024814+00:00
-- url     : https://prove2.me/submissions/1d107898-7226-49c4-8d9b-7c0477235b3b

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd10
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd10
theorem _root_.solution {l : Letter K S} {W : List (Letter K S)} (h : Good (l :: W)) :
    Good W ∧ l.intersection_update_fsHerm_neg_one ∉ W.map Letter.intersection_update_fsHerm_neg_one ∧ star l.pt = l.pt ∧ Reg W l.pt := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [List.map_cons, List.nodup_cons] at h1
  rw [List.pairwise_cons] at h3
  exact ⟨⟨h1.2, fun l' hl' => h2 l' (List.mem_cons_of_mem _ hl'), h3.2⟩, h1.1,
    h2 l List.mem_cons_self, h3.1⟩
end Formalism.FourierDecayAlt.P.Wd10

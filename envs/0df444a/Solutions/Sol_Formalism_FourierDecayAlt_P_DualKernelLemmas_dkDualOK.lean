-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DualKernelLemmas.dkDualOK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:26:34.673429+00:00
-- url     : https://prove2.me/submissions/9129e398-1d05-4e2f-9c80-0005c76ab091

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Theorems.Thm_Formalism_FourierDecayAlt_P_DualKernelLemmas_qw_append_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_DualKernelLemmas_good_tail

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DualKernelLemmas
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities
open scoped Matrix
namespace Formalism.FourierDecayAlt.P.DualKernelLemmas
theorem _root_.solution : DKDualOK := by
  intro S _ _ q w L hD
  induction L with
  | nil => trivial
  | cons l L ih =>
    obtain ⟨hP, hG, hGd, hPw, hq⟩ := hD
    have hl : l.plus = true := hP l (by simp)
    have hG' : Good (L ++ w) := good_tail hG
    have hGd' : Good (L.map dl ++ w) := good_tail (by simpa using hGd)
    have hpw := List.pairwise_cons.mp hPw
    refine ⟨?_, ?_, ih ⟨fun l' h => hP l' (by simp [h]), hG', hGd', hpw.2,
      fun l' h => hq l' (by simp [h])⟩⟩
    ·
      intro l' hl'
      have hdl : dl l = ⟨false, l.intersection_update_fsHerm_neg_one, l.pt + 1⟩ := by simp [dl, hl]
      rw [hdl]
      rcases List.mem_append.mp hl' with h | h
      · have hpl : l'.plus = true := hP l' (by simp [h])
        have := (hpw.1 l' h).1
        simp only [RegL, hpl, if_true]
        intro h0; apply this; linear_combination h0
      · have hgd : Good (dl l :: (L.map dl ++ w)) := by simpa using hGd
        have := (List.pairwise_cons.mp hgd.2.2).1 l' (by simp [h])
        rw [hdl] at this
        exact this
    · simp only [ypt, hl, if_true]
      refine qw_append_ne q w l.pt (hq l (by simp)) L fun l' hl' => ⟨hP l' (by simp [hl']), ?_, ?_⟩
      · exact (hpw.1 l' hl').1
      · intro h0; exact (hpw.1 l' hl').2.2 (by linear_combination h0)
end Formalism.FourierDecayAlt.P.DualKernelLemmas

-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.equal_roots_determinant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:44:02.22006+00:00
-- url     : https://prove2.me/submissions/8ce6c457-fc6e-40ce-b679-dc9c92be2a2d

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThresholdExponentEstimate
import Theorems.Thm_Formalism_FourierDecayAlt_P_det_weyl_matrix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C7.DEqualRoots := by
  intro s D'' c t z hs hz
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hz
  have e : (G.wMat (m + 1 - 1)).det = (G.wMat m).det := rfl
  rw [e, (det_weyl_matrix m).1, hz, Nat.add_sub_cancel]
  have h1 : ((-1 : ℂ)) ^ m * (-1) ^ (m + 1 + 1) = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨m + 1, by ring⟩
  linear_combination (-(D'' * (G.wMat m).det * c * t ^ m)) * h1
end Formalism.FourierDecayAlt.P

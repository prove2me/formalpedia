-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.sign_change_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:02:13.7566+00:00
-- url     : https://prove2.me/submissions/4b3416fa-9383-418c-b5aa-3ca06de760ba

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RhoAntitoneOfInterlacing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C7.SignCount := by
  unfold C7.SignCount
  intro ι _ f S hS hne
  classical
  rw [← Finset.prod_mul_prod_compl S f, ← mul_assoc]
  have h1 : (-1 : ℝ) ^ S.card * ∏ i ∈ S, f i = ∏ i ∈ S, (-f i) := by
    rw [Finset.prod_neg]
  rw [h1]
  apply mul_pos
  · exact Finset.prod_pos fun i hi => by linarith [(hS i).1 hi]
  · refine Finset.prod_pos fun i hi => ?_
    have h2 : ¬ f i < 0 := fun h => (Finset.mem_compl.1 hi) ((hS i).2 h)
    exact lt_of_le_of_ne (not_lt.1 h2) (hne i).symm
end Formalism.FourierDecayAlt.P

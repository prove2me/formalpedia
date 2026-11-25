-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.third_count_lemma_variant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:02:06.774927+00:00
-- url     : https://prove2.me/submissions/e5046d3c-8fca-4dd7-add5-c873d587a7c3

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdCountLemmaVariant

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
theorem _root_.solution : C7.LetterProductDoubleDegreeCount := by
  intro k r N d D hk h1 h2
  unfold C7.Dstar C7.Nprime C7.nOf at *
  have hn : 2 ≤ k + 2 * r + 1 := by omega
  have h3 : 3 * (r + 1) * d ≤ 3 * (r + 1) * ((N + 1) * (k + 2 * r + 1)) := Nat.mul_le_mul_left _ h1
  constructor
  · have e1 : (N + 1) * (r + 1) * (2 * (k + 2 * r + 1) + 2) + 3 * (r + 1) * ((N + 1) * (k + 2 * r + 1)) =
        ((r + 1) * (N + 1)) * (5 * (k + 2 * r + 1) + 2) := by ring
    have e2 : 6 * (r + 1) * (N + 1) * (k + 2 * r + 1) = ((r + 1) * (N + 1)) * (6 * (k + 2 * r + 1)) := by ring
    have h4 : ((r + 1) * (N + 1)) * (5 * (k + 2 * r + 1) + 2) ≤ ((r + 1) * (N + 1)) * (6 * (k + 2 * r + 1)) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  · have e2 : 6 * (r + 1) * (N + 1) * (k + 2 * r + 1) = ((r + 1) * (k + 2 * r + 1)) * (6 * (N + 1)) := by ring
    have e3 : 5 * (r + 1) * (3 * (N + 1) + 1) * (k + 2 * r + 1) =
        ((r + 1) * (k + 2 * r + 1)) * (5 * (3 * (N + 1) + 1)) := by ring
    rw [e2, e3]; exact Nat.mul_le_mul_left _ (by omega)
end Formalism.FourierDecayAlt.P

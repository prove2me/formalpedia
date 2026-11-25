-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.threshold_exponent_estimate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:06:56.286631+00:00
-- url     : https://prove2.me/submissions/746134e4-d2ee-4727-894d-8cefe5d46a2e

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThresholdExponentEstimate

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
theorem _root_.solution : C7.ThresholdE := by
  intro k r N AP hk hN hAP
  have h : 126 * (r + 1) ^ 3 * (C7.Nprime N * C7.nOf k r ^ 2 + C7.nOf k r ^ 3) +
      C7.B0 r * C7.mmP r (C7.Nprime N) (C7.nOf k r) + 12 * (r + 1) * C7.Nprime N * C7.nOf k r ≤
      915 * (r + 1) ^ 3 * (N * C7.nOf k r ^ 2 + C7.nOf k r ^ 3) := by
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hN
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hk
    unfold C7.Nprime C7.nOf C7.B0 C7.mmP
    refine le_trans (Nat.le_add_right _ (537*a*b^2*r^3 + 1611*a*b^2*r^2 + 1611*a*b^2*r + 537*a*b^2 + 2148*a*b*r^4 + 8592*a*b*r^3 + 12861*a*b*r^2 + 8502*a*b*r + 2085*a*b + 2148*a*r^5 + 10740*a*r^4 + 21426*a*r^3 + 21246*a*r^2 + 10434*a*r + 2022*a + 789*b^3*r^3 + 2367*b^3*r^2 + 2367*b^3*r + 789*b^3 + 5271*b^2*r^4 + 20706*b^2*r^3 + 30492*b^2*r^2 + 19950*b^2*r + 4893*b^2 + 11616*b*r^5 + 56568*b*r^4 + 110085*b*r^3 + 106926*b*r^2 + 51753*b*r + 9960*b + 8460*r^6 + 49248*r^5 + 119286*r^4 + 153702*r^3 + 110898*r^2 + 42339*r + 6645)) (le_of_eq ?_)
    ring
  have hR := (Nat.cast_le (α := ℝ)).2 h
  push_cast at hR
  linarith
end Formalism.FourierDecayAlt.P

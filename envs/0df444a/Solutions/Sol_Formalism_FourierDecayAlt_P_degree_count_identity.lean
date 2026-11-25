-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.degree_count_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:37:49.449106+00:00
-- url     : https://prove2.me/submissions/d71b44d8-1927-4d57-a9e9-1a739fc64251

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
theorem _root_.solution : C7.DegreeCount := by
  intro k r N M dl Dl hk hN hM h1 h2; unfold C7.Nprime C7.nOf at *
  have a2 : 1 ≤ (r + 1) * (k + 2 * r + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have a3 := Nat.mul_le_mul_left (6 * (3 * (N + 1))) a2
  have b1 : Dl ≤ (r + 1) * (k + 2 * r + 1) + 2 * (r + 1) := by nlinarith
  have b2 : 2 * M * Dl ≤ 2 * (3 * (N + 1)) * ((r + 1) * (k + 2 * r + 1) + 2 * (r + 1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 hM) b1
  have b3 : 2 * (3 * (N + 1)) * ((r + 1) * (k + 2 * r + 1) + 2 * (r + 1)) ≤
      6 * (r + 1) * (3 * (N + 1)) * (k + 2 * r + 1) := by
    have hP : (r + 1) * (N + 1) * 1 ≤ (r + 1) * (N + 1) * (k + 2 * r + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    nlinarith [hP]
  refine ⟨Nat.mul_le_mul (Nat.mul_le_mul_left 2 hM) h1, b2.trans b3, by nlinarith, by nlinarith, by nlinarith⟩
end Formalism.FourierDecayAlt.P

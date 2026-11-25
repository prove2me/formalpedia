-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.hermitian_curvature_degree_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:51:13.430291+00:00
-- url     : https://prove2.me/submissions/9e545aa3-8723-4f4e-8a14-237125bfa2c0

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
theorem _root_.solution : C7.DegreeCount2 := by
  intro k r N M dl Dl hk hN hM h1 h2
  unfold C7.Nprime C7.nOf at *
  have hn : 2 ≤ k + 2 * r + 1 := by omega
  have b2 : 2 * M * Dl ≤ 2 * (3 * (N + 1)) * ((r + 1) * (2 * (k + 2 * r + 1) + 2)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 hM) h2
  have b3 : 2 * (3 * (N + 1)) * ((r + 1) * (2 * (k + 2 * r + 1) + 2)) ≤
      6 * (r + 1) * (3 * (N + 1)) * (k + 2 * r + 1) := by
    have e1 : 2 * (3 * (N + 1)) * ((r + 1) * (2 * (k + 2 * r + 1) + 2)) =
        (6 * (r + 1) * (N + 1)) * (2 * (k + 2 * r + 1) + 2) := by ring
    have e2 : 6 * (r + 1) * (3 * (N + 1)) * (k + 2 * r + 1) =
        (6 * (r + 1) * (N + 1)) * (3 * (k + 2 * r + 1)) := by ring
    rw [e1, e2]; exact Nat.mul_le_mul_left _ (by omega)
  have a2 : 1 ≤ (r + 1) * (k + 2 * r + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  refine ⟨Nat.mul_le_mul (Nat.mul_le_mul_left 2 hM) h1, b2.trans b3, by nlinarith, by nlinarith⟩
end Formalism.FourierDecayAlt.P

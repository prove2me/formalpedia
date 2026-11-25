-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.each_level_counted_once
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:44:35.188146+00:00
-- url     : https://prove2.me/submissions/deb60dbd-ffd6-4a59-92c0-6f3ee2450f15

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionGivesUniformBoundsForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Jx6
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.OnceOnly := by
  intro P _ B hpos hk hA
  unfold S3.MassData.InTheoremA S3.MassData.Smod at hA
  obtain ⟨hk1, hk2⟩ := hk
  have hp := hpos.2
  have hvN : 0 < B.volN := by tauto
  have hvH : 0 < B.volH := by tauto
  have hvN' : 0 < B.volN' := by tauto
  have hvH' : 0 < B.volH' := by tauto
  have hd : 0 < B.dimπ := by tauto
  have hd' : 0 < B.dimπ' := by tauto
  have hn : 0 < B.n0c := by tauto
  have hs : 0 ≤ B.supdens := by tauto
  have c0 : 0 ≤ B.c0 * B.c0' := by unfold S3.MassData.c0 S3.MassData.c0'; positivity
  calc B.c0 * B.c0' * B.KV ≤ B.c0 * B.c0' * (B.supdens * B.n0c * B.KtopV) :=
        mul_le_mul_of_nonneg_left hk1 c0
    _ = B.supdens * B.n0c * (B.c0 * B.c0' * B.KtopV) := by ring
    _ ≤ B.supdens * B.n0c * ((1 + B.δ) * B.IntN) := mul_le_mul_of_nonneg_left hA (by positivity)
    _ = _ := by ring
end Formalism.FourierDecayAlt.P

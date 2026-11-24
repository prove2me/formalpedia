-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.aOf_pos_of_gapOK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:17:16.663797+00:00
-- url     : https://prove2.me/submissions/e21ce7c7-16a2-46da-81aa-5593bcc2eb9f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CkOnZeroOfContOn
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbConvDDOfDecDD
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_ag_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_gap4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
namespace Formalism.FourierDecayAlt.P.S3dx4
theorem _root_.solution {k r : ℕ} {h : ℝ} (hG : GapOK k r h) : 0 < aOf r h := by
  have h4 := gap4 hG
  have h5 := ag_nonneg k r
  have : (0 : ℝ) ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  linarith
end Formalism.FourierDecayAlt.P.S3dx4

-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.ag_lt_a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:54:46.317796+00:00
-- url     : https://prove2.me/submissions/01080d1d-375c-4075-8519-23e970f94ea6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L1QuotientIntegralBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiRegOf
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_ag_nonneg


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
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
namespace Formalism.FourierDecayAlt.P.S3dx4
theorem _root_.solution {k r : ℕ} {h : ℝ} (hG : GapOK k r h) : AG k r < aOf r h := by
  have h1 := hG.2.2.2
  have h2 := ag_nonneg k r
  have h3 : 0 ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  linarith
end Formalism.FourierDecayAlt.P.S3dx4

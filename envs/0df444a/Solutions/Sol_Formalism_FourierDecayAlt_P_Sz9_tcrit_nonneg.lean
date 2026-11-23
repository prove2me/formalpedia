-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz9.tcrit_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:59.243876+00:00
-- url     : https://prove2.me/submissions/ab9f13ce-aaf6-4221-986c-23c168ed898a

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaBoundOnBoundary
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmRingIdempotentUnitRatioIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SixteenMulLeTwoPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz9
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz9
theorem _root_.solution (k m : ℕ) (ka rd g VV Vu : ℝ) (hka : 0 < ka) (hrd : 0 < rd) (hg : 0 < g)
    (hVV : 0 < VV) (hVu : 0 < Vu) : 0 ≤ Tcrit k m ka rd g VV Vu := by
  unfold Tcrit
  apply Real.rpow_nonneg
  unfold TcritPow
  positivity
end Formalism.FourierDecayAlt.P.Sz9

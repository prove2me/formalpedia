-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz3.hs_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:37.3398+00:00
-- url     : https://prove2.me/submissions/144e2484-58fe-4be8-9bb1-4e103a95495e

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_hs_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz3
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz3
theorem _root_.solution (p J : ℕ) (h : p ≤ J) : hs p ≤ hs J := by
  have := hs_sub p J h
  have h0 : 0 ≤ ∑ d ∈ Ioc p J, 1 / (d : ℝ) := Finset.sum_nonneg (fun d _ => by positivity)
  linarith
end Formalism.FourierDecayAlt.P.Sz3

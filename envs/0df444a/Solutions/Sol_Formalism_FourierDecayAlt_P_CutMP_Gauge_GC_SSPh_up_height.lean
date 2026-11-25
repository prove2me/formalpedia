-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSPh.up_height
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:15:21.111145+00:00
-- url     : https://prove2.me/submissions/3db4b063-c35a-4fc2-bbf8-416f73024b86

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTSSCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTSSPhaseA
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_SSPh_sum_ind

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.M Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSPh
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSPh
theorem _root_.solution (P : M.Par) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (ρ ρ' : M.Ty P) (hU : M.Up P l ρ ρ') :
    height P ρ' = height P ρ + 1 := by
  unfold height
  rw [Finset.sum_congr rfl (fun i _ => hU i), Finset.sum_add_distrib, sum_ind P l hl]
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSPh

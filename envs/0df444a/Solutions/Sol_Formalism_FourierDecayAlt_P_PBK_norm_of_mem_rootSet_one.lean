-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.norm_of_mem_rootSet_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:47:11.300915+00:00
-- url     : https://prove2.me/submissions/ac4311c0-8ea5-481e-afea-8e2d348644d4

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormOfMemRootSetOne
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBK_mem_rootSet__178724779aab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open MeasureTheory Filter Topology Set Polynomial
noncomputable section
open Classical
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution {s : ℕ} (hs : s ≠ 0) {ζ : ℂ} (hζ : ζ ∈ G.rootSet s 1) : ‖ζ‖ = 1 := by
  exact Complex.norm_eq_one_of_pow_eq_one ((Formalism.FourierDecayAlt.P.PBK.mem_rootSet' hs).mp hζ) hs
end Formalism.FourierDecayAlt.P.PBK

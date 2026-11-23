-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.dimension_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:42:03.93074+00:00
-- url     : https://prove2.me/submissions/8c241617-5935-47d2-b24e-3a2a1994b081

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Theorems.Thm_Formalism_FourierDecayAlt_P_G1_card_UT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G1
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.DimCount := by
  intro n
  constructor
  · rw [card_UT, mul_comm]; exact Finset.sum_range_id_mul_two n
  · rw [card_UT, card_UT, Finset.sum_range_succ]; ring
end Formalism.FourierDecayAlt.P

-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.sumRanks
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:40.280804+00:00
-- url     : https://prove2.me/submissions/27fa4e98-d8cb-4b52-a8a1-88779f5fcac8

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz1_half_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz1_sum_Ioc_odd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.Sz Formalism.FourierDecayAlt.P.Sz1
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Sz.SumRanks := by
  intro k r m n hm hn
  subst hm
  have hn' : n = k + (2 * r + 1) := by omega
  subst hn'
  have h1 : 2 * r + 2 - 1 = 2 * r + 1 := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [half_eq, sum_Ioc_odd, h1]
  · rw [Nat.card_Ioc]; omega
  · rw [half_eq, h1]; ring
end Formalism.FourierDecayAlt.P
